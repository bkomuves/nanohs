
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#define MAX(a,b)   (((a)>=(b))?(a):(b))

#define STACK_SIZE   (  1024*1024)
#define HEAP_SIZE    (8*1024*1024)

typedef uint64_t *heap_ptr;
typedef uint64_t *stack_ptr;

heap_ptr  HP, Heap_begin , Heap_end;
stack_ptr SP, Stack_begin, Stack_end;

// c stack debugging
uint64_t rsp_begin, rsp_last;
register uint64_t rsp asm ("rsp");

uint64_t Last_compacted_heap_size;

#define DE_BRUIJN_FROM(sptr,k) ((heap_ptr)(sptr[-k-1]))
#define DE_BRUIJN(k)           DE_BRUIJN_FROM(SP,k)

// arguments come on stack
typedef heap_ptr generic_fun_t();

// We would need to align static function pointers, so we just introduce
// an extra indirection and use indices for simplicity. We also need the arities.
int       NStatic;
void    **StaticFunPointers;
int      *StaticFunArities;
char    **ConstructorNames;
char    **StaticStringTable;
stack_ptr static_stack;

// command line arguments
int    ArgCount;
char **ArgVector;

// pointer tagging
#define PTAG_PTR  0       // allocated heap object 
#define PTAG_INT  1       // 61 bit integer (or char) literal
#define PTAG_FUN  2       // static function - index, not pointer!
#define PTAG_CON  4       // nullary data constructor
#define PTAG_FILE 7       // FILE handle, or more generally foreign ptr (must be aligned)

// header word tagging
#define HTAG_CLOS  0      // closure
#define HTAG_FWDP  2      // forwarding pointer
#define HTAG_DCON  4      // data constructor

// heap object tag word
#define TAGWORD_DATACON(con_tag,con_arity)             (                    ((con_arity)<<16) | ((con_tag  ) << 3) | HTAG_DCON )
#define TAGWORD_CLOSURE(stat_idx, env_size,rem_arity)  ( ((stat_idx)<<32) | ((env_size )<<16) | ((rem_arity) << 3) | HTAG_CLOS )

#define PTAG_OF(ptr)       (((int64_t)(ptr)) & 0x07)
#define HAS_PTAG(ptr,tag)  (PTAG_OF(ptr) == (tag))
#define IS_HEAP_PTR(ptr)   HAS_PTAG(ptr,PTAG_PTR)

#define NULLARY_CON(con) ( (heap_ptr)(uint64_t) (((con)<<3) + PTAG_CON) )
#define INT_LITERAL(i)   ( (heap_ptr)(uint64_t) ((( (uint64_t)(i) )<<3) + PTAG_INT) )
#define CHR_LITERAL(c)   INT_LITERAL(c)

#define TO_INT(ptr)      (((int64_t)(ptr))>>3)
#define FROM_INT(i)      ((heap_ptr)(uint64_t)(((i)<<3) + PTAG_INT))

#define TO_BOOL(ptr)     (((int64_t)(ptr))>>3)
#define FROM_BOOL(b)     ((heap_ptr)(uint64_t)(((b)<<3) + PTAG_CON))

#define TO_STATIDX(ptr)  (((uint64_t)(ptr))>>3)
#define FROM_STATIDX(j)  ((heap_ptr)(uint64_t)(((j)<<3) + PTAG_FUN))

#define TO_FILE(ptr)     ((FILE*) ((((intptr_t)ptr)>>3)<<3) )
#define FROM_FILE(fptr)  ( (heap_ptr) ( ((intptr_t)fptr) | PTAG_FILE ) )

#define CON_False    0
#define CON_True     1
#define CON_Unit     2
#define CON_Nil      3
#define CON_Cons     4
#define CON_Nothing  5
#define CON_Just     6
#define CON_ReadMode        7
#define CON_WriteMode       8
#define CON_AppendMode      9
#define CON_ReadWriteMode  10
#define CON_IO             11

#define FALSE    NULLARY_CON( CON_False   )
#define TRUE     NULLARY_CON( CON_True    )
#define UNIT     NULLARY_CON( CON_Unit    )
#define NIL      NULLARY_CON( CON_Nil     )
#define NOTHING  NULLARY_CON( CON_Nothing )

#define false 0
#define true  1

// -----------------------------------------------------------------------------
// error handling

heap_ptr rts_internal_error(const char *msg) {
  fputs("[RTS] ",stderr);
  fputs(msg,stderr);
  fputc(10 ,stderr);
  exit(999);
  return UNIT;
}

// -----------------------------------------------------------------------------
// raw allocation

heap_ptr malloc_words(int nwords) {
  heap_ptr ptr = (heap_ptr) malloc( 8 * nwords );
  if (!ptr)                          rts_internal_error("fatal: malloc failed"); 
  if ((((intptr_t)ptr) & 0x07) != 0) rts_internal_error("fatal: malloc not aligned"); 
  return ptr;
}

// -----------------------------------------------------------------------------
// garbage collection

heap_ptr New_Heap_begin;
heap_ptr New_HP;

heap_ptr rts_gc_worker(heap_ptr root) {
  switch(PTAG_OF(root)) {

    // closure or data constructor
    case PTAG_PTR: { 
      uint64_t tagword = root[0];
      int size = (tagword >> 16) & 0xffff;      // payload size
      int htag = tagword & 0x07;
      switch(htag) {
        case HTAG_FWDP: return (heap_ptr) ((tagword>>3)<<3);  // forwarding pointer
        case HTAG_CLOS: break;                                // closure
        case HTAG_DCON: break;                                // data constructor
        default: 
          printf("root = %p | header = %llx | htag = %d | size = %d\n",root,tagword,htag,size);
          rts_internal_error("gc found an invalid heap object");
      }
      heap_ptr tgt = New_HP;
      New_HP += (size+1);
      tgt[0] = root[0];                       // copy header
      root[0] = ((uint64_t)tgt) | 0x02;       // set forwarding pointer
      // copy payload
      for(int i=0; i<size; i++) { tgt[i+1] = (uint64_t) rts_gc_worker( (heap_ptr) root[i+1] ); }   
      return tgt;
    } 

    // not an allocated heap object
    default: return root;
  }
} 

void rts_perform_gc() {
  printf("performing GC...\n");

  uint64_t cur_heap_size = HP - Heap_begin;
  uint64_t new_heap_size = MAX( cur_heap_size , 3 * Last_compacted_heap_size );

// printf("old heap: %p -> %p\n",Heap_begin,HP);
printf("old heap size = %llu words\n",cur_heap_size);
printf("new heap size = %llu words\n",new_heap_size);

  New_Heap_begin = malloc_words(new_heap_size);
  New_HP = New_Heap_begin;

  int stack_len = SP - Stack_begin;
  for(int j=0;j<stack_len;j++) { 
    Stack_begin[j] = (uint64_t) rts_gc_worker( (heap_ptr) Stack_begin[j] ); 
  }

  // we need this because there can be thunks ??
  for(int j=0;j<NStatic;j++) { 
    // printf("%d | %llu\n", j, New_HP - New_Heap_begin);
    static_stack[j] = (uint64_t) rts_gc_worker( (heap_ptr) static_stack[j] ); 
  }

  free(Heap_begin);
  Heap_begin = New_Heap_begin;
  Heap_end   = Heap_begin + new_heap_size;
  HP         = New_HP;
  Last_compacted_heap_size = HP - Heap_begin;

printf("compacted heap size = %llu words\n",Last_compacted_heap_size);
}

// -----------------------------------------------------------------------------
// allocation

// #define SP_GRANULARITY (   512*1024)
// #define HP_GRANULARITY (8*1024*1024)
// heap_ptr SP_threshold;
// heap_ptr HP_threshold;

heap_ptr rts_heap_allocate(int size) {
  heap_ptr obj = HP;
  HP += size;
//    // heap debugging
//    if (HP >= HP_threshold) {
//      int k = HP_threshold - Heap_begin;
//      int mb = k / 1024/1024;
//      fprintf(stderr,"HP threshold: %d million words\n",mb);
//      HP_threshold = HP_threshold + HP_GRANULARITY;
//    }
  if (HP >= Heap_end) { 
    // rts_internal_error("heap overflow");
    HP = obj;
    rts_perform_gc();
    obj = HP;
    HP += size;
  } 
  return obj;
}

stack_ptr rts_stack_allocate(int size) {

  int k = rsp_last - rsp;
  if (k >= 1024*1024) {
    rsp_last = rsp;
    printf("c stack size = %llu bytes\n" , rsp_begin - rsp);
  }

  stack_ptr loc = SP;
  SP += size;
  if (SP >= Stack_end) rts_internal_error("stack overflow");
  return loc;
}

heap_ptr rts_allocate_datacon(int con_tag, int con_arity) {
  heap_ptr obj = rts_heap_allocate(con_arity + 1);
  obj[0] = TAGWORD_DATACON(con_tag,con_arity);
  return obj;
}

heap_ptr rts_allocate_closure(uint64_t statidx, int env_size, int rem_arity) {
  heap_ptr obj = rts_heap_allocate(env_size + 1);
  obj[0] = TAGWORD_CLOSURE(statidx,env_size,rem_arity);
  return obj;
}

// -----------------------------------------------------------------------------
// marshalling

int rts_marshal_to_cstring(int nmax, char *target, heap_ptr source) {
  heap_ptr ptr = source;
  int i = 0;
  while( i < nmax-1 && IS_HEAP_PTR(ptr) && (ptr[0] == TAGWORD_DATACON(CON_Cons,2)) ) {
    int c = TO_INT(ptr[1]);
    target[i++] = c;
    ptr = (heap_ptr)(ptr[2]);
  }  
  target[i] = 0;
  return i;
}

heap_ptr rts_marshal_from_cstring(const char *str) {
  char c = str[0];
  if (c != 0) {
    heap_ptr obj = rts_allocate_datacon(CON_Cons,2);
    obj[1] = (uint64_t) CHR_LITERAL(c);
    obj[2] = (uint64_t) rts_marshal_from_cstring(str+1);
    return obj;
  }
  else return NIL;
}

// -----------------------------------------------------------------------------
// generic print

// closures can be refer to themselves, so we need some kind of "gas" 
void rts_generic_print_limited(heap_ptr obj, int budget) {
  switch(PTAG_OF(obj)) {
    case PTAG_INT:   printf("%lld",(int64_t)(TO_INT(obj)));  break;
    case PTAG_FUN:   printf("static_%lld",TO_STATIDX(obj));  break;
    case PTAG_FILE:  printf("FILE(%p)",TO_FILE(obj));        break;
    case PTAG_CON: {
      // nullary constructor
      int64_t word = (int64_t)obj;
      int con_idx = (word & 0xffff) >> 3;
      printf("%s/0",ConstructorNames[con_idx]);
      break;
    }
    case PTAG_PTR: {
      // fputs("TODO: implement generic print for heap objects",stdout);
      uint64_t tagword = obj[0];
      switch(tagword & 0x07) {
        // data constructor
        case HTAG_DCON: {
          int con_idx   = (tagword & 0xffff) >> 3;
          int con_arity = (tagword >> 16) & 0xffff;
          printf("(%s/%d",ConstructorNames[con_idx],con_arity);
          if (budget > 0) {
            for(int i=0;i<con_arity;i++) {
              printf(" ");
              rts_generic_print_limited( (heap_ptr) obj[i+1] , budget-1);
            }
            printf(")");
          }
          break;
        }
        // closure
        case HTAG_CLOS: {
          int rem_arity = (tagword & 0xffff) >> 3;
          int env_size  = (tagword >> 16) & 0xffff;
          int stat_idx  = (tagword >> 32);
          printf("CLOSURE(static_%d/%d/%d)",stat_idx,env_size,rem_arity);
          if (budget > 0) {
            for(int i=0;i<env_size;i++) {
              if (i==0) printf("["); else printf(","); 
              rts_generic_print_limited( (heap_ptr) obj[env_size-i] , budget-1);  // env is now in opposite order!
            }
            printf("]");
          }
          break;
        }
      }
      break;
    }
    default: printf("<INVALID>"); break;
  }
}

void rts_generic_print(heap_ptr obj) {
  rts_generic_print_limited(obj,10);
}

void rts_generic_println(heap_ptr obj) {
  rts_generic_print(obj);
  printf("\n");
}

void rts_debug_println(const char *str, heap_ptr obj) {
  printf("%s >>> ",str);
  rts_generic_println(obj);
}

// -----------------------------------------------------------------------------
// generic application

heap_ptr rts_static_call(int statidx) {
  void *funptr = StaticFunPointers[statidx];
  generic_fun_t *fun = (generic_fun_t*)funptr;
  return (*fun)();
}

//heap_ptr rts_static_call(void *funptr) {
//  generic_fun_t *fun = (generic_fun_t*)funptr;
//  return (*fun)();
//}

// these are mutually recursive
heap_ptr rts_apply_worker(int static_arity, int statfun, int env_size, uint64_t *env, int nargs);
heap_ptr rts_apply       (heap_ptr funobj, int nargs);

// arguments are on the stack, in *reverse order*, and environment is also in reverse order
heap_ptr rts_apply_worker(int static_arity, int statfun, int env_size, uint64_t *env, int nargs) {
//printf("rts_apply_worker %d <%d> %d %d\n",static_arity,statfun,env_size,nargs);
  int ntotal = env_size + nargs;
  if (ntotal == static_arity) {
    // saturated call
    // stack_ptr frame = SP - nargs;
    stack_ptr mid   = rts_stack_allocate( env_size );
    for(int i=0; i<env_size; i++) { mid[i] = env[i]; }
    heap_ptr result = rts_static_call( statfun );
    return result;
  }
  if (ntotal < static_arity) {
    // undersaturated call
    stack_ptr frame = SP - nargs;
    heap_ptr obj = rts_allocate_closure( statfun , ntotal , static_arity - ntotal);
    for(int j=0; j<nargs   ; j++) { obj[      j+1] = frame[j]; }
    for(int i=0; i<env_size; i++) { obj[nargs+i+1] = env  [i]; }
    SP -= nargs;  // there is no callee to free the arguments, so we have to do it!
    return obj;
  }
  else {
    // oversaturated call
    int this_arity = static_arity - env_size;
    int rem_arity  = ntotal - static_arity;
    // stack_ptr frame = SP - nargs;
    heap_ptr mid = rts_stack_allocate( env_size );
    for(int i=0; i<env_size; i++) { mid[i] = env[i]; }
    heap_ptr result1 = rts_static_call( statfun );
    heap_ptr result2 = rts_apply( result1 , rem_arity ) ;
    return result2;
  }
}

// arguments are on the stack
heap_ptr rts_apply(heap_ptr funobj, int nargs) {
  stack_ptr args = SP - nargs;
  switch(PTAG_OF(funobj)) {

    // closure or data constructor
    case PTAG_PTR: { 
      uint64_t tagword = funobj[0];
      switch(tagword & 0x07) {
        // closure
        case HTAG_CLOS: {
          int rem_arity = (tagword & 0xffff) >> 3;
          int env_size  = (tagword >> 16) & 0xffff;
          int statfun   = (tagword >> 32);
          return rts_apply_worker( env_size+rem_arity, statfun, env_size, funobj+1, nargs);
        }
        // data constructor
        case HTAG_DCON: {
          int con       = (tagword & 0xffff) >> 3;
          int old_arity = (tagword >> 16) & 0xffff;
          heap_ptr obj = rts_allocate_datacon(con, old_arity+nargs);
          for(int i=0;i<old_arity;i++) { obj[i+1]           = funobj[i+1];        }
          for(int j=0;j<nargs    ;j++) { obj[old_arity+1+j] = args  [nargs-j-1];  }  // arguments are opposite order, but constructors fields are not?
          SP -= nargs;  // there is no callee to free the arguments, so we have to do it!
          return obj;
        }
        default: {
          int size = (tagword & 0xffff) >> 3;
          int htag = tagword & 0x07;
          printf("funobj = %p | header = %llx | htag = %d | size = %d\n",funobj, tagword,htag,size);
          return rts_internal_error("application to an invalid heap object");
        }
    } }

    // nullary constructor
    case PTAG_CON: {
      int con = ((int64_t)funobj) >> 3;
      heap_ptr obj = rts_allocate_datacon(con,nargs);
      for(int i=0;i<nargs;i++) { obj[i+1] = args[nargs-i-1]; }
      SP -= nargs;  // there is no callee to free the arguments, so we have to do it!
      return obj;
    }

    // static function
    case PTAG_FUN: {
      int static_idx = ((int64_t)funobj) >> 3;
      int   arity  = StaticFunArities [static_idx];
      return rts_apply_worker( arity, static_idx, 0, NULL, nargs);
    }

    default:
      // rts_generic_println(funobj);
      return rts_internal_error("application to a literal constant");
  }
}

// -----------------------------------------------------------------------------
// force thunks (only used when there are non-lambdas present in letrec)

heap_ptr rts_force_value(heap_ptr obj) {
  switch(PTAG_OF(obj)) {
    // closure or data constructor
    case PTAG_PTR: {
      uint64_t tagword = obj[0];
      switch(tagword & 0x07) {
        // closure
        case HTAG_CLOS: {
          int rem_arity = (tagword & 0xffff) >> 3;
          int env_size  = (tagword >> 16) & 0xffff;
          if (rem_arity > 0) { return obj; } else {
            int statfun  = (tagword >> 32);
            return rts_apply_worker( env_size, statfun, env_size, obj+1, 0);
          } }
        // data con
        default: return obj;
    } }
    // static function (still can be a CAF)
    case PTAG_FUN: { 
      int static_idx = ((int64_t)obj) >> 3;
      int arity = StaticFunArities[static_idx];
      if (arity>0) { return obj; } else { 
        return rts_static_call(static_idx);   // CAF
    } }
    // anything else
    default: return obj;
  }
}

heap_ptr rts_force_thunk_at(stack_ptr ptr) {
  heap_ptr old = (heap_ptr)ptr[0];
  heap_ptr val = rts_force_value(old);
  ptr[0] = (uint64_t) val;
  return val;
}

// -----------------------------------------------------------------------------
// generic equality

int rts_generic_eq(heap_ptr arg1, heap_ptr arg2) {
  // printf("generic equality\n");
  switch ( IS_HEAP_PTR(arg1) + 2*IS_HEAP_PTR(arg2) ) {
    case 0:
      // both is a machine word
      return ( (intptr_t)(arg1) == (intptr_t)(arg2) );

    case 3: {
      // both is an allocated heap object
      if (arg1[0] != arg2[0]) return false;
      int tagword = arg1[0];
      int tag = tagword & 0x07;
      if ((tag != 0) && (tag != 4)) rts_internal_error("fatal: generic equality: invalid heap object");
      int size  = (tagword >> 16) & 0xffff;
      for(int i=0;i<size;i++) { if (!rts_generic_eq( (heap_ptr)arg1[i+1] , (heap_ptr)arg2[i+1] )) return false; }
      return true;
    } 

    default:
      return false;     // one is real heap object, the other is a machine word
  } 
}

// -----------------------------------------------------------------------------
// initialization

void rts_initialize(int argc, char **argv) {
  printf("[rts version = C99]\n");
  if (sizeof(void*) != 8) { rts_internal_error("fatal: expecting a 64 bit architecture"); }

  ArgCount  = argc;
  ArgVector = argv;

  rsp_begin = rsp;
  rsp_last  = rsp_begin;

  // at the moment we allocate a closure (1 word) for each static function
  // which is stupid, whatever...
  int heap_size = MAX( HEAP_SIZE , 128 + NStatic );

  Stack_begin = (heap_ptr) malloc_words( STACK_SIZE );
  Heap_begin  = (heap_ptr) malloc_words( heap_size  );
  Stack_end   = Stack_begin + STACK_SIZE;
  Heap_end    = Heap_begin  + heap_size;
  SP = Stack_begin;
  HP = Heap_begin;
  Last_compacted_heap_size = heap_size;

//  SP_threshold = SP;
//  HP_threshold = HP;
//
  // initialize static stack. This simulates a top-level letrec, but with a 
  // letrec we couldn't really optimize the fully static function calls?
  static_stack = (heap_ptr) malloc_words( NStatic );
  for(int i=0;i<NStatic;i++) {
    int   arity  = StaticFunArities [i];
    static_stack[i] = (uint64_t) FROM_STATIDX(i); 
  }

//   // evaluate thunks (this includes functions which looks like CAFs!!!)
//   for(int i=0;i<NStatic;i++) {
//     // printf("%d\n",i);
//     int   arity  = StaticFunArities [i];
//     if (arity == 0) { 
//       // thunk; we have to evaluate it
// //      printf("evaluating static thunk %d\n",i);
//       heap_ptr obj = rts_static_call(i); // funptr);
//       static_stack[i] = (uint64_t)obj;   
//     }
//   } 

  // printf("initialized.\n");
}

// -----------------------------------------------------------------------------
// primops

heap_ptr prim_Negate (heap_ptr arg1) { return FROM_INT ( - TO_INT (arg1) ); }
heap_ptr prim_Not    (heap_ptr arg1) { return FROM_BOOL( ! TO_BOOL(arg1) ); }

heap_ptr prim_Plus   (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) + TO_INT(arg2) ); }
heap_ptr prim_Minus  (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) - TO_INT(arg2) ); }
heap_ptr prim_Times  (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) * TO_INT(arg2) ); }
heap_ptr prim_Div    (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) / TO_INT(arg2) ); }
heap_ptr prim_Mod    (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) % TO_INT(arg2) ); }

heap_ptr prim_BitAnd (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) & TO_INT(arg2) ); }
heap_ptr prim_BitOr  (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) | TO_INT(arg2) ); }
heap_ptr prim_BitXor (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) ^ TO_INT(arg2) ); }
heap_ptr prim_ShiftL (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) << TO_INT(arg2) ); }
heap_ptr prim_ShiftR (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) >> TO_INT(arg2) ); }

heap_ptr prim_Chr    (heap_ptr arg1) { return arg1; }
heap_ptr prim_Ord    (heap_ptr arg1) { return arg1; }

heap_ptr prim_GenEQ  (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL(rts_generic_eq(arg1,arg2)); }

heap_ptr prim_IntEQ  (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_INT(arg1) == TO_INT(arg2) ); } 
heap_ptr prim_IntLT  (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_INT(arg1) <  TO_INT(arg2) ); } 
heap_ptr prim_IntLE  (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_INT(arg1) <= TO_INT(arg2) ); } 

// heap_ptr prim_And   (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_BOOL(arg1) && TO_BOOL(arg2) ); } 
// heap_ptr prim_Or    (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_BOOL(arg1) || TO_BOOL(arg2) ); } 
// heap_ptr prim_IFTE  (heap_ptr argb, heap_ptr arg1, heap_ptr arg2) { 
//   if TO_BOOL(argb) { return arg1; } else { return arg2; } 
// }

// -----------------------------------------------------------------------------

// // runIO :: IO a -> a
// heap_ptr prim_RunIO(heap_ptr funobj) {
//   // recall that "type IO a = (Unit -> a)"
//   stack_ptr loc = rts_stack_allocate(1);
//   loc[0] = (uint64_t) UNIT;
//   return rts_apply( funobj , 1 );
// }  

// runIO :: IO a -> a
heap_ptr prim_RunIO(heap_ptr arg) {
  printf("[rts version = C99]\n");
  // recall that "data IO a = IO (Unit -> a)"
  heap_ptr ptr = rts_force_value(arg);
  if( IS_HEAP_PTR(ptr) && (ptr[0] == TAGWORD_DATACON(CON_IO,1)) ) {
    heap_ptr funobj = (heap_ptr) ptr[1];
    stack_ptr loc = rts_stack_allocate(1);
    loc[0] = (uint64_t) UNIT;
    return rts_apply( funobj , 1 );
  }  
  else {
    fprintf(stderr,"PROBLEM:\n");
    rts_generic_println(arg); 
    rts_internal_error("runIO: argument is not an IO action");
    return UNIT;
  }
}

// -----------------------------------------------------------------------------

// getChar# :: Unit -> Maybe Char
heap_ptr prim_GetChar(heap_ptr arg1) {
  int c = getchar();
  if (c==EOF) { return NOTHING; } else { 
    heap_ptr obj = rts_allocate_datacon(CON_Just,1);
    obj[1] = (uint64_t)(CHR_LITERAL(c));
    return obj;
  }
}

// putChar# :: Char -> Unit
heap_ptr prim_PutChar(heap_ptr arg1) {
  putchar(TO_INT(arg1));
  return UNIT;
}

// exit# :: Int -> Unit
heap_ptr prim_Exit(heap_ptr arg1) {
  exit(TO_INT(arg1));
  return UNIT;
}

// print# :: String -> Unit
heap_ptr prim_Print(heap_ptr arg1) {
  rts_generic_println(arg1);
  return UNIT;
}

// error# :: String -> a
heap_ptr prim_Error(heap_ptr arg1) {
  heap_ptr ptr = arg1;
  fputc('*',stderr);
  fputc('*',stderr);
  fputc('*',stderr);
  fputc(' ',stderr);
  while( IS_HEAP_PTR(ptr) && (ptr[0] == TAGWORD_DATACON(CON_Cons,2)) ) {
    int c = TO_INT(ptr[1]);
    fputc(c,stderr);
    ptr = (heap_ptr)(ptr[2]);
  }  
  fputc('\n',stderr);
  exit(666);
  return UNIT;
}

// getArg# :: Int -> Maybe String
heap_ptr prim_GetArg(heap_ptr arg1) {
  int j = TO_INT(arg1);
  if ( (j >= 0) && (j < ArgCount - 1) ) {
    heap_ptr obj = rts_allocate_datacon(CON_Just,1);
    obj[1] = (uint64_t) rts_marshal_from_cstring(ArgVector[j+1]); 
    return obj;
  }
  return NOTHING;
}

// -----------------------------------------------------------------------------

char *file_modes[] = { "r" , "w" , "a" , "rw" };

const char* c_file_mode_str(heap_ptr con) { 
  switch ((uint64_t)(con)) {
    case ( PTAG_CON + (CON_ReadMode     <<3) ): return file_modes[0];
    case ( PTAG_CON + (CON_WriteMode    <<3) ): return file_modes[1];
    case ( PTAG_CON + (CON_AppendMode   <<3) ): return file_modes[2];
    case ( PTAG_CON + (CON_ReadWriteMode<<3) ): return file_modes[3];
  }
  rts_internal_error("invalid file IO mode"); return NULL;
}

heap_ptr prim_StdIn () { return (FROM_FILE(stdin )); }
heap_ptr prim_StdOut() { return (FROM_FILE(stdout)); }
heap_ptr prim_StdErr() { return (FROM_FILE(stderr)); }

// hOpenFile# :: FilePath -> IOMode -> Handle
heap_ptr prim_OpenFile(heap_ptr fnarg, heap_ptr modearg) {
  const char *mode = c_file_mode_str(modearg);
  char fname[256];
  rts_marshal_to_cstring(256,fname,fnarg);
  FILE *handle = fopen(fname,mode);
  if (!handle) {
    char msg[512]; 
    sprintf(msg,"cannot open file `%s`",fname);
    rts_internal_error(msg);
  }
  return (FROM_FILE(handle));
}

// hGetChar# :: Handle -> Maybe Char
heap_ptr prim_HGetChar(heap_ptr harg) {
  FILE *h = TO_FILE(harg);
  int c = fgetc( h );
//  printf("||| hGetChar: %p %d\n",h,c);
  if (c==EOF) { return NOTHING; } else { 
    heap_ptr obj = rts_allocate_datacon(CON_Just,1);
    obj[1] = (uint64_t)(CHR_LITERAL(c));
    return obj;
  }
}

// hPutChar# :: Handle -> Char -> Unit
heap_ptr prim_HPutChar(heap_ptr harg, heap_ptr carg) {
  fputc( TO_INT(carg) , TO_FILE(harg) );
  return UNIT;
}

// hPutStr# :: Handle -> String -> Unit
heap_ptr prim_HPutStr(heap_ptr harg, heap_ptr sarg) {
  char *cstr;
  rts_marshal_to_cstring( 1024 , cstr, sarg );
  fputs( cstr , TO_FILE(harg) );
  return UNIT;
}

// hClose# :: Handle -> Unit
heap_ptr prim_HClose(heap_ptr harg) {
  fclose( TO_FILE(harg) );
  return UNIT;
}


// -----------------------------------------------------------------------------


