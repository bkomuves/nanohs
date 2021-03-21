
; MacOS syscalls

rts_exit: 
FROM_INT_LITERAL 
mov rdi,rax 
mov rax, 0x2000001   ; exit 
syscall 
retn 

rts_putchar_stderr: 
mov rdi,2   ; stderr = 2 
jmp rts_local_hputchar_literal

rts_putchar: 
mov rdi,1   ; stdout = 1 
; jmp rts_local_hputchar_literal

rts_local_hputchar_literal: 
FROM_INT_LITERAL   ; FROM_CHR_LITERAL 
rts_local_hputchar: 
push rax 
mov rsi,rsp  
mov rdx,1   ; length = 1 character  
mov rax,0x2000004   ; write  
syscall 
pop rax 
mov rax,NULLARY_CON(CON_Unit)   ; Unit 
retn

rts_getchar: 
mov rdi,0   ; stdin = 0
call rts_local_hgetchar
test rax,rax
js .error
TO_INT_LITERAL   ; TO_CHR_LITERAL
mov rdx,rax
ALLOCATE_DATACON CON_Just,1   ; Just
mov [rax+8],rdx
retn
.error:
mov rax,NULLARY_CON(CON_Nothing)   ; Nothing 
retn

; returns a character code or -1 if error
rts_local_hgetchar: 
push rax    ; alloca 8 bytes
mov rsi,rsp ; buffer 
mov rdx,1   ; length = 1 character  
mov rax,0x2000003   ; read  
syscall
or rax,rax     ; bytes read (0 or 1)
jnz .succeed
pop rdx
xor rax,rax
dec rax        ; -1 = error
retn
.succeed:
pop rax 
retn

; rsi = string ; rdx = length of the string
rts_local_stderr_string:
mov rdi,2   ; stderr = 2 
mov rax,0x2000004   ; write  
syscall 
retn

rts_error: 
IS_HEAP_PTR
jnz .exit
cmp rax,TAG_DATACON(CON_Cons,2)   ; Cons cell
jnz .exit
push rax
mov rax,rax[8]
call rts_putchar_stderr
pop rax
mov rax,rax[16]
jmp rts_error
.exit:
mov rdi,666          ; exit code 
mov rax, 0x2000001   ; exit 
syscall 
retn 
