SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x10 ]
test al, al
adox rcx, r11
adox r14, r8
adox r9, r13
mov rdx, 0xd838091dd2253531 
mulx r8, r11, r10
mov r8, 0xfffffffefffffc2f 
mov rdx, r11
mulx r13, r11, r8
mov r8, 0xffffffffffffffff 
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, r8
adcx r11, r10
mov r11, rdi
seto r10b
mov rdx, -0x2 
inc rdx
adox r11, r13
mov r13, rdi
adox r13, r15
adox rdi, r15
adcx r11, rcx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
adcx r13, r14
adcx rdi, r9
setc dl
clc
adcx rcx, r11
movzx r14, r10b
lea r14, [ r14 + rbx ]
seto bl
mov r10, -0x2 
inc r10
adox rbp, r8
mov r9b, dl
mov rdx, [ rax + 0x10 ]
mulx r8, r11, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x28 ], r14
mulx r14, r10, rcx
mov r14, 0xfffffffefffffc2f 
mov rdx, r14
mov byte [ rsp - 0x20 ], r9b
mulx r9, r14, r10
adox r11, r12
adcx rbp, r13
adox r8, [ rsp - 0x30 ]
adcx r11, rdi
movzx r12, bl
lea r12, [ r12 + r15 ]
mov r15, 0xffffffffffffffff 
mov rdx, r10
mulx rbx, r10, r15
seto r13b
movzx rdi, byte [ rsp - 0x20 ]
mov rdx, 0x0 
dec rdx
adox rdi, rdx
adox r12, [ rsp - 0x28 ]
mov rdi, r10
seto dl
mov r15, -0x2 
inc r15
adox rdi, r9
mov r9, r10
adox r9, rbx
adcx r8, r12
adox r10, rbx
mov r12, 0x0 
adox rbx, r12
movzx r12, r13b
mov r15, [ rsp - 0x38 ]
lea r12, [ r12 + r15 ]
mov r15, -0x2 
inc r15
adox r14, rcx
adox rdi, rbp
movzx r14, dl
adcx r14, r12
seto cl
inc r15
adox rdi, [ rsp - 0x40 ]
setc bpl
clc
mov r13, -0x1 
movzx rcx, cl
adcx rcx, r13
adcx r11, r9
adcx r10, r8
adcx rbx, r14
mov rdx, [ rsi + 0x10 ]
mulx r8, r9, [ rax + 0x10 ]
mov rdx, 0xd838091dd2253531 
mulx rcx, r12, rdi
mov rdx, [ rax + 0x0 ]
mulx r14, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ rax + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], rbx
mulx rbx, rcx, r12
setc dl
clc
adcx r15, [ rsp - 0x48 ]
mov [ rsp - 0x8 ], rcx
mov cl, dl
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x0 ], bpl
mov [ rsp + 0x8 ], r14
mulx r14, rbp, [ rax + 0x18 ]
adcx r9, r13
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x10 ], cl
mulx rcx, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r13
mulx r13, rcx, [ rsi + 0x18 ]
adox r15, r11
adcx rbp, r8
mov rdx, 0x0 
adcx r14, rdx
adox r9, r10
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r10, r11, r12
mov r8, r11
clc
adcx r8, rbx
mov r12, r11
adcx r12, r10
adcx r11, r10
mov rbx, 0x0 
adcx r10, rbx
clc
adcx rcx, [ rsp + 0x8 ]
movzx rbx, byte [ rsp + 0x10 ]
movzx rdx, byte [ rsp + 0x0 ]
lea rbx, [ rbx + rdx ]
adcx r13, [ rsp + 0x20 ]
adox rbp, [ rsp - 0x10 ]
setc dl
clc
adcx rdi, [ rsp - 0x8 ]
mov dil, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], rcx
mulx rcx, r13, [ rsi + 0x18 ]
adcx r8, r15
adcx r12, r9
adcx r11, rbp
adox r14, rbx
adcx r10, r14
setc dl
clc
mov r15, -0x1 
movzx rdi, dil
adcx rdi, r15
adcx r13, [ rsp + 0x18 ]
mov r9, 0x0 
adcx rcx, r9
movzx rbx, dl
adox rbx, r9
xor rdi, rdi
adox r8, [ rsp - 0x18 ]
mov r9, 0xd838091dd2253531 
mov rdx, r8
mulx rbp, r8, r9
mov rbp, 0xfffffffefffffc2f 
xchg rdx, rbp
mulx rdi, r14, r8
adox r12, [ rsp + 0x30 ]
adox r11, [ rsp + 0x28 ]
adox r13, r10
adox rcx, rbx
mov r10, 0xffffffffffffffff 
mov rdx, r8
mulx rbx, r8, r10
mov rdx, r8
adcx rdx, rdi
seto dil
inc r15
adox r14, rbp
mov r14, r8
adcx r14, rbx
adox rdx, r12
adox r14, r11
adcx r8, rbx
adcx rbx, r15
adox r8, r13
adox rbx, rcx
movzx rbp, dil
adox rbp, r15
mov r12, rdx
mov r11, 0xfffffffefffffc2f 
sub r12, r11
mov r13, r14
sbb r13, r10
mov rdi, r8
sbb rdi, r10
mov rcx, rbx
sbb rcx, r10
sbb rbp, 0x00000000
cmovc rdi, r8
cmovc r12, rdx
cmovc r13, r14
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r13
cmovc rcx, rbx
mov [ rbp + 0x18 ], rcx
mov [ rbp + 0x0 ], r12
mov [ rbp + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6899
; seed 4338427508481979 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1235542 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=121, initial num_batches=31): 78393 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06344826804754512
; number reverted permutation / tried permutation: 66780 / 90270 =73.978%
; number reverted decision / tried decision: 59639 / 89729 =66.466%
; validated in 3.421s
