SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 176
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r9, r8, rax
mov r9, 0xfffffffefffffc2f 
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r14
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r14
mulx r14, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox rbp, r10
adox r11, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r10, [ rsi + 0x18 ]
adox r10, rcx
mov rdx, 0x0 
adox r12, rdx
adcx r9, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], rcx
mulx rcx, r14, rdx
mov rdx, -0x2 
inc rdx
adox r14, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r14
mulx r14, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], rax
mulx rax, r13, [ rsi + 0x8 ]
adox r8, rcx
adox r13, r14
mov rdx, 0x0 
adox rax, rdx
mov rcx, r15
mov r14, -0x3 
inc r14
adox rcx, rbx
mov rbx, r15
adox rbx, rdi
adcx rcx, rbp
adcx rbx, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, rbp, [ rsi + 0x10 ]
adox r15, rdi
mov rdx, 0x0 
adox rdi, rdx
adcx r15, r10
adcx rdi, r12
mov r10, -0x3 
inc r10
adox r9, r11
mov rdx, [ rsi + 0x10 ]
mulx r12, r10, rdx
adox r10, [ rsp - 0x8 ]
adox r12, [ rsp - 0x10 ]
setc dl
clc
adcx rcx, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x18 ]
adcx r8, r15
adcx r13, rdi
mov r11, [ rsp - 0x28 ]
mov r15, 0x0 
adox r11, r15
movzx rdi, dl
adcx rdi, rax
mov rdx, [ rsi + 0x0 ]
mulx r15, rax, [ rsi + 0x18 ]
inc r14
adox r15, [ rsp - 0x30 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp + 0x0 ], r15
mulx r15, r14, rcx
mov r15, 0xfffffffefffffc2f 
mov rdx, r15
mov [ rsp + 0x8 ], rax
mulx rax, r15, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r12
mulx r12, r11, r14
mov r14, r11
setc dl
clc
adcx r14, rax
mov rax, [ rsp - 0x38 ]
adox rax, [ rsp - 0x40 ]
mov [ rsp + 0x20 ], rax
seto al
mov byte [ rsp + 0x28 ], dl
mov rdx, -0x2 
inc rdx
adox r15, rcx
adox r14, rbx
seto r15b
inc rdx
adox rbp, r14
mov rcx, r11
adcx rcx, r12
adcx r11, r12
adcx r12, rdx
mov rbx, 0xd838091dd2253531 
mov rdx, rbx
mulx r14, rbx, rbp
clc
mov r14, -0x1 
movzx r15, r15b
adcx r15, r14
adcx r8, rcx
adcx r11, r13
adox r9, r8
adox r10, r11
adcx r12, rdi
movzx r13, byte [ rsp + 0x28 ]
mov rdi, 0x0 
adcx r13, rdi
mov r15, 0xfffffffefffffc2f 
mov rdx, rbx
mulx rcx, rbx, r15
mov r8, 0xffffffffffffffff 
mulx rdi, r11, r8
mov rdx, r11
clc
adcx rdx, rcx
mov rcx, r11
adcx rcx, rdi
adcx r11, rdi
adox r12, [ rsp + 0x18 ]
mov r14, 0x0 
adcx rdi, r14
clc
adcx rbx, rbp
adcx rdx, r9
adcx rcx, r10
adcx r11, r12
adox r13, [ rsp + 0x10 ]
adcx rdi, r13
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, rbp, rdx
seto dl
dec r14
movzx rax, al
adox rax, r14
adox rbp, [ rsp - 0x48 ]
setc al
clc
adcx rbx, [ rsp + 0x8 ]
adcx rcx, [ rsp + 0x0 ]
adcx r11, [ rsp + 0x20 ]
adcx rbp, rdi
movzx r10, al
movzx rdx, dl
lea r10, [ r10 + rdx ]
mov r12, 0x0 
adox r9, r12
mov rdx, 0xd838091dd2253531 
mulx rax, r13, rbx
mov rdx, r13
mulx r13, rax, r15
mov rdi, -0x3 
inc rdi
adox rax, rbx
mulx rbx, rax, r8
adcx r9, r10
mov r10, rax
setc dl
clc
adcx r10, r13
mov r13, rax
adcx r13, rbx
adcx rax, rbx
adox r10, rcx
adox r13, r11
adox rax, rbp
adcx rbx, r12
adox rbx, r9
movzx rcx, dl
adox rcx, r12
mov r11, r10
sub r11, r15
mov rbp, r13
sbb rbp, r8
mov rdx, rax
sbb rdx, r8
mov r9, rbx
sbb r9, r8
sbb rcx, 0x00000000
cmovc rdx, rax
cmovc r11, r10
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], r11
cmovc r9, rbx
cmovc rbp, r13
mov [ rcx + 0x8 ], rbp
mov [ rcx + 0x10 ], rdx
mov [ rcx + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7840
; seed 3239295316300738 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1025551 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=171, initial num_batches=31): 76334 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07443218328488783
; number reverted permutation / tried permutation: 76571 / 90290 =84.806%
; number reverted decision / tried decision: 64249 / 89709 =71.619%
; validated in 1.97s
