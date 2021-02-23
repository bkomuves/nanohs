
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#define STACK_SIZE    (1024*1024)
#define HEAP_SIZE  (64*1024*1024)

typedef uint64_t *heap_ptr;
typedef uint64_t *stack_ptr;

heap_ptr  Heap_ptr , Heap_begin , Heap_end;
stack_ptr Stack_ptr, Stack_begin, Stack_end;

#define DE_BRUIJN(k) ((heap_ptr)(Stack_ptr[-k-1]))

typedef heap_ptr generic_fun_t();  // (int, uint64_t*);

// We need to align static function pointers, so we just introduce
// an extra indirection for simplicity. We also need the arities.
void **StaticFunPointers;
int   *StaticFunArities;

// pointer tagging
#define PTAG_PTR  0       // allocated heap object 
#define PTAG_INT  1       // 61 bit integer (or char) literal
#define PTAG_FUN  2       // static function - index, not pointer!
#define PTAG_CON  4       // nullary data constructor

// heap object tag word
#define HTAG_DATACON(con_tag,con_arity)   (((con_arity)<<16) + ((con_tag  ) << 3) + 4)
#define HTAG_CLOSURE(env_size,rem_arity)  (((env_size )<<16) + ((rem_arity) << 3) + 0)

#define PTAG_OF(ptr)       (((intptr_t)(ptr)) & 0x07)
#define HAS_PTAG(ptr,tag)  (PTAG_OF(ptr) == (tag))
#define IS_HEAP_PTR(ptr)   HAS_PTAG(ptr,PTAG_PTR)

#define NULLARY_CON(con) ( (heap_ptr)(intptr_t) (((con)<<3) + PTAG_CON) )
#define INT_LITERAL(i)   ( (heap_ptr)(intptr_t) (((i  )<<3) + PTAG_INT) )
#define CHR_LITERAL(c)   INT_LITERAL(c)

#define TO_INT(ptr)      (((intptr_t)(ptr))>>3)
#define FROM_INT(i)      ((heap_ptr)(intptr_t)(((i)<<3) + PTAG_INT))

#define TO_BOOL(ptr)     (((intptr_t)(ptr))>>3)
#define FROM_BOOL(b)     ((heap_ptr)(intptr_t)(((b)<<3) + PTAG_CON))

#define TO_STATIDX(ptr)  (((uint64_t)(intptr_t)(ptr))>>3)
#define FROM_STATIDX(j)  ((heap_ptr)(intptr_t)(((j)<<3) + PTAG_FUN))

#define CON_False   0
#define CON_True    1
#define CON_Unit    2
#define CON_Nil     3
#define CON_Cons    4
#define CON_Nothing 5
#define CON_Just    6

#define FALSE    NULLARY_CON( CON_False   )
#define TRUE     NULLARY_CON( CON_True    )
#define UNIT     NULLARY_CON( CON_Unit    )
#define NIL      NULLARY_CON( CON_Nil     )
#define NOTHING  NULLARY_CON( CON_Nothing )

#define false 0
#define true  1

// -----------------------------------------------------------------------------

heap_ptr rts_internal_error(const char *msg) {
  fputs(msg,stderr);
  exit(999);
  return UNIT;
}

heap_ptr rts_heap_allocate(int size) {
  heap_ptr obj = Heap_ptr;
  Heap_ptr += size;
  if (Heap_ptr >= Heap_end) rts_internal_error("heap overflow");
  return obj;
}

stack_ptr rts_stack_allocate(int size) {
  stack_ptr loc = Stack_ptr;
  Stack_ptr += size;
  if (Stack_ptr >= Stack_end) rts_internal_error("stack overflow");
  return loc;
}

heap_ptr rts_allocate_datacon(int con_tag, int con_arity) {
  heap_ptr obj = rts_heap_allocate(con_arity + 1);
  obj[0] = HTAG_DATACON(con_tag,con_arity);
  return obj;
}

heap_ptr rts_allocate_closure(void *fun_ptr, int env_size, int rem_arity) {
  heap_ptr obj = rts_heap_allocate(env_size + 2);
  obj[0] = HTAG_CLOSURE(env_size,rem_arity);
  obj[1] = (intptr_t)(fun_ptr);
  return obj;
}

void rts_initialize() {
  Stack_begin = (heap_ptr) malloc( 8 * STACK_SIZE );
  Heap_begin  = (heap_ptr) malloc( 8 * HEAP_SIZE  );
  Stack_end   = Stack_begin + STACK_SIZE;
  Heap_end    = Heap_begin  + HEAP_SIZE;
  Stack_ptr   = Stack_begin;
  Heap_ptr    = Heap_begin;
}

// -----------------------------------------------------------------------------
// generic application

heap_ptr rts_generic_call(void *funptr) { //  , int nargs, uint64_t *args) {
  generic_fun_t *fun = (generic_fun_t*)funptr;
  return (*fun)(); // nargs,args);
}

// these are mutually recursive
heap_ptr rts_apply_worker(int static_arity, void *funptr, int env_size, uint64_t *env, int nargs, uint64_t *args);
heap_ptr rts_apply       (heap_ptr funobj, int nargs, uint64_t *args);

heap_ptr rts_apply_worker(int static_arity, void *funptr, int env_size, uint64_t *env, int nargs, uint64_t *args) {
  int ntotal = env_size + nargs;
  if (ntotal == static_arity) {
    // saturated call
    stack_ptr tmp = rts_stack_allocate( ntotal );
    for(int i=0;i<env_size ;i++) { tmp[i]          = env [i]; }
    for(int j=0;j<nargs    ;j++) { tmp[env_size+j] = args[j]; }
    heap_ptr result = rts_generic_call( funptr ); // , env_size+nargs , tmp );
    Stack_ptr = tmp; 
    return result;
  }
  if (ntotal < static_arity) {
    // unsaturated call
    heap_ptr obj = rts_allocate_closure(funptr, ntotal , static_arity - ntotal);
    for(int i=0;i<env_size ;i++) { obj[i+2]          = env [i]; }
    for(int j=0;j<nargs    ;j++) { obj[env_size+2+j] = args[j];   }
    return obj;
  }
  else {
    // oversaturated call
    int rem_arity = ntotal - static_arity;
    stack_ptr tmp = rts_stack_allocate( static_arity );
    for(int i=0;i<env_size ;i++) { tmp[i]          = env [i]; }
    for(int j=0;j<rem_arity;j++) { tmp[env_size+j] = args[j];   }
    heap_ptr result1 = rts_generic_call( funptr ); // , static_arity , tmp );
    heap_ptr result2 = rts_apply( result1 , rem_arity , args + (static_arity-env_size) ) ;
    Stack_ptr = tmp; 
    return result2;
  }
}

heap_ptr rts_apply(heap_ptr funobj, int nargs, uint64_t *args) {
  switch(PTAG_OF(funobj)) {

    // closure or data constructor
    case PTAG_PTR: { 
      uint64_t tagword = funobj[0];
      switch(tagword & 0x07) {
        // closure
        case 0: {
          int rem_arity = (tagword & 0xffff) >> 3;
          int env_size  = (tagword >> 16) & 0xffff;
          void *funptr  = (void*) funobj[1];
          return rts_apply_worker( env_size+rem_arity, funptr, env_size, funobj+2, nargs, args);
        }
        // data constructor
        case 4: {
          int con       = (tagword & 0xffff) >> 3;
          int old_arity = (tagword >> 16) & 0xffff;
          heap_ptr obj = rts_allocate_datacon(con, old_arity+nargs);
          for(int i=0;i<old_arity;i++) { obj[i+1]           = funobj[i+1]; }
          for(int j=0;j<nargs    ;j++) { obj[old_arity+1+j] = args  [j];   }
          return obj;
        }
        default:
          return rts_internal_error("application to an invalid heap object");
    } }

    // nullary constructor
    case PTAG_CON: {
      int con = ((intptr_t)funobj) >> 3;
      heap_ptr obj = rts_allocate_datacon(con,nargs);
      for(int i=0;i<nargs;i++) { obj[i+1] = args[i]; }
      return obj;
    }

    // static function
    case PTAG_FUN: {
      int static_idx = ((intptr_t)funobj) >> 3;
      void *funptr = StaticFunPointers[static_idx];
      int   arity  = StaticFunArities [static_idx];
      return rts_apply_worker( arity, funptr, 0, NULL, nargs, args );
    }

    default:
      return rts_internal_error("application to a literal constant");
  }
}

// -----------------------------------------------------------------------------
// force thunks (only used when there are non-lambdas present in letrec)

heap_ptr rts_force_thunk(heap_ptr obj) {
  switch(PTAG_OF(obj)) {
    // closure or data constructor
    case PTAG_PTR: {
      uint64_t tagword = obj[0];
      switch(tagword & 0x07) {
        // closure
        case 0: {
          int rem_arity = (tagword & 0xffff) >> 3;
          int env_size  = (tagword >> 16) & 0xffff;
          if (rem_arity > 0) { return obj; } else {
            void *funptr  = (void*) obj[1];
            return rts_apply_worker( env_size, funptr, env_size, obj+2, 0, NULL );
        } }
        // data con
        default: return obj;
    } }
    // static function (still can be a CAF)
    case PTAG_FUN: { 
      int static_idx = ((intptr_t)obj) >> 3;
      void *funptr = StaticFunPointers[static_idx];
      int   arity  = StaticFunArities [static_idx];
      if (arity>0) { return obj; } else { 
        return rts_generic_call(funptr); // , 0, NULL); // CAF
    } }
    // anything else
    default: return obj;
  }
}

// -----------------------------------------------------------------------------
// generic equality

int rts_generic_eq(heap_ptr arg1, heap_ptr arg2) {
  switch ( IS_HEAP_PTR(arg1) + 2*IS_HEAP_PTR(arg2) ) {
    case 0:
      // both is a machine word
      return ( (intptr_t)(arg1) == (intptr_t)(arg2) );

    case 3: {
      // both is an allocated heap object
      if (arg1[0] != arg2[0]) return false;
      int tagword = arg1[0];
      switch(tagword & 0x07) {
        // closure
        case 0: {
          int env_size  = (tagword >> 16) & 0xffff;
          if (arg1[1] != arg2[1]) return false;
          for(int i=0;i<env_size;i++) { if (!rts_generic_eq( (heap_ptr)arg1[i+2] , (heap_ptr)arg2[i+2] )) return false; }
          return true;
        }
        // data constructor
        case 4: {
          int arity = (tagword >> 16) & 0xffff;
          for(int i=0;i<arity;i++) { if (!rts_generic_eq( (heap_ptr)arg1[i+1] , (heap_ptr)arg2[i+1] )) return false; }
          return true;
        }
        // invalid
        default: 
          return false;  
    } }

    default:
      return false;     // one is real heap object, the other is a machine word
  } 
}

// -----------------------------------------------------------------------------
// generic print

void rts_generic_print(heap_ptr obj) {
  switch(PTAG_OF(obj)) {
    case PTAG_INT:
      printf("%lld",(int64_t)(TO_INT(obj)));
      break;
    case PTAG_FUN:
      printf("static_%lld",TO_STATIDX(obj));
      break;
    case PTAG_CON: {
      // nullary constructor
      int64_t x = (int64_t)((intptr_t)obj);
      x = x>>3;
      switch(x) {
        case CON_False:   printf("False"  ); break;
        case CON_True:    printf("True"   ); break;
        case CON_Unit:    printf("Unit"   ); break;
        case CON_Nothing: printf("Nothing"); break;
        case CON_Nil:     printf("Nil"    ); break;
        default:
          printf("CON(%lld)", x);
      }
      break;
    }
    case PTAG_PTR:
      fputs("TODO: implement generic print for heap objects",stdout);
      break;
  }
}

void rts_generic_println(heap_ptr obj) {
  rts_generic_print(obj);
  printf("\n");
}

// -----------------------------------------------------------------------------

heap_ptr prim_Neg   (heap_ptr arg1) { return FROM_INT ( - TO_INT (arg1) ); }
heap_ptr prim_Not   (heap_ptr arg1) { return FROM_BOOL( ! TO_BOOL(arg1) ); }

heap_ptr prim_Plus  (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) + TO_INT(arg2) ); }
heap_ptr prim_Minus (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) - TO_INT(arg2) ); }
heap_ptr prim_Times (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) * TO_INT(arg2) ); }
heap_ptr prim_Div   (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) / TO_INT(arg2) ); }
heap_ptr prim_Mod   (heap_ptr arg1, heap_ptr arg2) { return FROM_INT( TO_INT(arg1) % TO_INT(arg2) ); }

heap_ptr prim_Chr   (heap_ptr arg1) { return arg1; }
heap_ptr prim_Ord   (heap_ptr arg1) { return arg1; }

heap_ptr prim_GenEQ (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL(rts_generic_eq(arg1,arg2)); }

heap_ptr prim_IntEQ (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_INT(arg1) == TO_INT(arg2) ); } 
heap_ptr prim_IntLT (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_INT(arg1) <  TO_INT(arg2) ); } 
heap_ptr prim_IntLE (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_INT(arg1) <= TO_INT(arg2) ); } 

heap_ptr prim_And   (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_BOOL(arg1) && TO_BOOL(arg2) ); } 
heap_ptr prim_Or    (heap_ptr arg1, heap_ptr arg2) { return FROM_BOOL( TO_BOOL(arg1) || TO_BOOL(arg2) ); } 

heap_ptr prim_IFTE  (heap_ptr argb, heap_ptr arg1, heap_ptr arg2) { 
  if TO_BOOL(argb) { return arg1; } else { return arg2; } 
}

// -----------------------------------------------------------------------------

// getChar :: Unit -> Maybe Char
heap_ptr prim_GetChar(heap_ptr arg1) {
  int c = getchar();
  if (c==EOF) { return NOTHING; } else { 
    heap_ptr obj = rts_allocate_datacon(CON_Just,1);
    obj[1] = (uint64_t)(CHR_LITERAL(c));
    return obj;
  }
}

// putChar :: Char -> Unit
heap_ptr prim_PutChar(heap_ptr arg1) {
  putchar(TO_INT(arg1));
  return UNIT;
}

// exit :: Int -> Unit
heap_ptr prim_Exit(heap_ptr arg1) {
  exit(TO_INT(arg1));
  return UNIT;
}

// error :: String -> a
heap_ptr prim_Error(heap_ptr arg1) {
  heap_ptr ptr = arg1;
  while( IS_HEAP_PTR(ptr) && (ptr[0] == HTAG_DATACON(CON_Cons,2)) ) {
    int c = TO_INT(ptr[1]);
    fputc(c,stderr);
    ptr = (heap_ptr)(ptr[2]);
  }  
  exit(666);
  return UNIT;
}

// -----------------------------------------------------------------------------

