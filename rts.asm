
;
; RTS conventions
; ===============
; A) On the heap, we can have 1) closures/PAPs and 2) data constructors  
;    these are distinguished by bit #2. We reserve bits #0/#1 for GC.
;     * for closures, the second word is the function pointer, and the rest
;       is the environment / partially applied arguments
;     * for data constructors, the tag is simply followed by the arguments.
; B) Heap pointers can be actual pointers or objects fitting in a machine word.
;    Since heap pointers are aligned, we can use the low 3 bits to distinguish
;    between these.:
;     * low bits = 000 means an actual heap pointer
;     * low bits = 001 means a 61 bit literal (int or char). 
;     * low bits = 010 means a static function pointer
;     * low bits = 100 means a nullary data constructor
;    This means that static functions must be aligned too
; C) We have a custom stack to store the enviroment. The stack pointer is RBP
;    Arguments are always passed on this stack
;

bits 64
global start 

section .bss

align 8
heap:  resb (1024*1024*128)   ; 128 mb
stack: resq (1024*1024)       ; 8 mb      

section .data

errmsg_app: db  "runtime error: invalid application",10
.len:       equ $ - errmsg_app

section .text

%define CON_False   0
%define CON_True    1
%define CON_Unit    2
%define CON_Nil     3
%define CON_Cons    4
%define CON_Nothing 5
%define CON_Just    6

%define HEAP_PTR       r15
%define STACK_PTR      rbp
%define STACK_PTR_COPY r14
%define ARG0  rax
%define ARG1  rcx
%define ARG2  rdx

%define DE_BRUIJN(idx)        qword [ STACK_PTR      - 8*(idx+1) ]
%define DE_BRUIJN_COPY(idx)   qword [ STACK_PTR_COPY - 8*(idx+1) ]
%macro PUSH 1
  mov [STACK_PTR],%1
  add STACK_PTR,8
%endmacro
%macro POP 1
  sub STACK_PTR,8
  mov %1,[STACK_PTR]
%endmacro

%define INT_LITERAL(i)   (i<<3) + 1
%define CHR_LITERAL(c)   INT_LITERAL(c)
%define NULLARY_CON(con) (con<<3) + 4

%define IS_HEAP_PTR  test al,7

%define FROM_INT_LITERAL      sar rax,3
%define FROM_INT_LITERAL_ARG0 sar ARG0,3
%define FROM_INT_LITERAL_ARG1 sar ARG1,3
%macro  FROM_INT_LITERAL_ARGS01 0
  FROM_INT_LITERAL_ARG0
  FROM_INT_LITERAL_ARG1
%endmacro
%macro TO_INT_LITERAL 0
  shl rax,3
  or al,1
%endmacro

%define FROM_BOOL_CON      shr rax,3
%define FROM_BOOL_CON_ARG0 shr ARG0,3
%define FROM_BOOL_CON_ARG1 shr ARG1,3
%macro  FROM_BOOL_CON_ARGS01 0
  FROM_BOOL_CON_ARG0
  FROM_BOOL_CON_ARG1
%endmacro
%macro TO_BOOL_CON 0
  shl rax,3
  or al,2
%endmacro
 
%define FROM_STATIC_FUNPTR    and al,0xf8
%define TO_STATIC_FUNPTR      or  al,2

%define TAG_DATACON(con_tag ,con_arity)  (con_arity<<16) + (con_tag   << 3) + 4
%define TAG_CLOSURE(env_size,rem_arity)  (env_size <<16) + (rem_arity << 3) + 0

; args: size in words
%macro ALLOCATE_HEAP 1
  mov rax,HEAP_PTR
  add HEAP_PTR , (8 * %1)
%endmacro

%macro DYN_ALLOCATE_HEAP 1
  mov rax,%1
  shl rax,3
  add rax,HEAP_PTR
  xchg rax,HEAP_PTR
%endmacro

; args: static label, env size, rem_arity
%macro ALLOCATE_CLOSURE 3
  ALLOCATE_HEAP (%2 + 2)  
  mov rdx,TAG_CLOSURE(%2,%3)
  mov [rax],rdx
  mov rdx,%1
  mov [rax+8],rdx
%endmacro

%macro DYN_ALLOCATE_CLOSURE 3
  mov rax,%1
  add rax,2
  shl rax,3
  add rax,HEAP_PTR
  xchg rax,HEAP_PTR
  mov rdx,%2  ; env size
  shl rdx,13
  add rdx,%3  ; rem arity
  shl rdx,3
  mov [rax],rdx
  mov rdx,%1
  mov [rax+8],rdx
%endmacro

; args: con_tag, con_arity
%macro ALLOCATE_DATACON 2
  ALLOCATE_HEAP (%2 + 1)  
  mov rdx,TAG_DATACON(%1,%2)
  mov [rax],rdx
%endmacro

; args: con_tag, con_arity
%macro DYN_ALLOCATE_DATACON 2
  mov rax,%1
  inc rax
  shl rax,3
  add rax,HEAP_PTR
  xchg rax,HEAP_PTR
  mov rdx,%2  ; con arity
  shl rdx,13
  add rdx,%1  ; con tag
  shl rdx,3
  mov [rax],rdx
%endmacro

;-------------------------------------------------------------------------------

  . "; evaluate a thunk on RAX"
rts_eval_thunk:
IS_HEAP_PTR
jne .singleword
mov rdx,[rax]
test dx,dx       ; thunk = low 3 bits is zero and the next 13 bits too
jnz .evaluated
.thunk:
push rsi
push rdi
mov rsi,rax
mov rcx,[rsi]
shr rcx,16       ; size of the environment
push rcx
lea rdi,[rsi+16]
.push_loop:
mov rax,[rdi]
PUSH rax
add rdi,8
loop .push_loop
call [rsi+8]
pop rcx
sub STACK_PTR,rcx
pop rdi
pop rsi
retn
.singleword:
mov dl,al
and dl,7
cmp dl,2
je .static_funptr
.evaluated:
retn
.static_funptr:
mov rbx,rax
and bl,0xf8
mov rcx,[rbx-8]    ; env size / arity
or rcx,rcx         ; both is zero?
jnz .evaluated
call rbx           ; example: CAF like a string. No environment, no arguments
retn 

;---------------------------------------

; apply to an unknown function. RAX = heap ptr to function
; RCX = number of arguments on the stack (assumed to be positive!)
rts_apply:
IS_HEAP_PTR
jne .single_word  ; either a literal or a static function ptr
mov rdx,[rax]     ; tag word
test dl,7
jz .closure

.single_word:
mov dl,al
and dl,7
cmp dl,2
jne .app_to_nonlambda
.static_funptr:
; TODO: maybe jump to somewhere in the middle of .closure to solve this?

; fatal error: application to non-lambda and non-constructor
.app_to_nonlambda:
mov rsi,errmsg_app
mov rdx,errmsg_app.len
call rts_local_stderr_string
mov rax,666
jmp rts_exit

.datacon:
mov rsi,rax
mov r8,rdx
mov r9,rdx
shr r8,16
and r8,0xffff    ; r8 = con tag
shr r9,3
and r9,0x1fff    ; r9 = old arity
mov r10,r9
add r10,rcx      ; r10 = new arity
DYN_ALLOCATE_DATACON r8,r10
mov rdi,rax
push rcx
mov rcx,r9
mov rbx,8
.copy_old_args:
mov rax,[rsi+rbx]
mov [rdi+rbx],rax
add rbx,8
.loop copy_old_args
pop rcx
.copy_new_args:
mov rax,[STACK_PTR-8*rcx+8]
mov [rdi+rbx],rax
add rbx,8
.loop copy_new_args
mov rax,rdi
retn

.closure:
mov r8,rdx
mov r9,rdx
shr r8,16
and r8,0xffff    ; r8 = env size
shr r9,3        
and r9,0x1fff    ; r9 = arity
cmp rcx,r9       ; actual args vs arity
je  .equal
jl  .less
jmp .greater

; TODO: push the environment then push the arguments then call (callee frees)
.equal:
push rax
or r8,r8
jz .do_not_insert_env
mov rsi,STACK_PTR
lea rdi,[STACK_PTR + r8 * 8]
.move_args_loop:
sub rsi,8
sub rdi,8
mov rax,[rsi]
mov [rdi],rax
loop .move_args_loop:
mov rcx,r8
mov rdi,rsi
pop rsi
push rsi
add rsi,8
rep movsq
.do_not_insert_env:
pop rax
jmp rax

; TODO: allocate closure, copy the environment then copy the arguments
.less:

; TODO: push the environment then push the necessary arguments then call;
;       then recursively call rts_apply for the remaining args
.greater:


