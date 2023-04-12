SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
add r15, r9
adcx rax, rdi
adcx r11, r10
mov rdx, 0xffffffff00000000 
mulx r9, r10, rbx
mov rdi, 0xffffffff 
mov rdx, rbx
mov [ rsp - 0x48 ], r13
mulx r13, rbx, rdi
mov rdi, -0x2 
inc rdi
adox rbp, r9
adox rbx, r12
mov r12, 0x0 
adox r13, r12
mov r9, -0x3 
inc r9
adox rdx, r8
adox r10, r15
adox rbp, rax
adcx rcx, r12
adox rbx, r11
mov rdx, [ rsi + 0x8 ]
mulx r15, r8, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rax, [ rsi + 0x0 ]
clc
adcx rax, r10
adox r13, rcx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, [ rsi + 0x8 ]
seto dl
inc rdi
adox r8, r11
adcx r8, rbp
adox r10, r15
adox r12, rcx
adox r9, rdi
adcx r10, rbx
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mulx r15, rbx, [ rsi + 0x8 ]
adcx r12, r13
movzx rdx, bpl
adcx rdx, r9
mov r11, -0x3 
inc r11
adox rbx, r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, rdx
adox rbp, r15
mov rdx, 0xffffffffffffffff 
mulx r9, rcx, rax
mov rdx, [ rsi + 0x10 ]
mulx r15, r9, [ rsi + 0x18 ]
adox r9, r13
adox r15, rdi
mov rdx, 0xffffffff00000000 
mulx rdi, r13, rcx
mov r11, 0xffffffff 
mov rdx, rcx
mov [ rsp - 0x40 ], r15
mulx r15, rcx, r11
mov r11, rdx
mov [ rsp - 0x38 ], r9
mov r9, -0x2 
inc r9
adox r11, rax
mov r11, 0xffffffffffffffff 
mulx r9, rax, r11
setc dl
clc
adcx rax, rdi
adcx rcx, r9
mov rdi, 0x0 
adcx r15, rdi
adox r13, r8
adox rax, r10
adox rcx, r12
adox r15, r14
clc
adcx r13, [ rsp - 0x48 ]
movzx r8, dl
adox r8, rdi
mov rdx, r11
mulx r10, r11, r13
mov r10, r11
mov r12, -0x3 
inc r12
adox r10, r13
adcx rbx, rax
mov rdx, [ rsi + 0x8 ]
mulx r14, r10, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mulx rax, r9, r11
adcx rbp, rcx
adcx r15, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, rcx, [ rsi + 0x0 ]
adcx r8, [ rsp - 0x40 ]
mov rdx, 0xffffffff00000000 
mulx r12, rdi, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
setc dl
clc
adcx r10, r13
adcx rcx, r14
adox rdi, rbx
mov bl, dl
mov rdx, [ rsi + 0x18 ]
mulx r13, r14, rdx
adcx r14, r8
mov rdx, 0xffffffff 
mov byte [ rsp - 0x20 ], bl
mulx rbx, r8, r11
mov r11, 0x0 
adcx r13, r11
clc
adcx r9, r12
adox r9, rbp
adcx r8, rax
adox r8, r15
adcx rbx, r11
adox rbx, [ rsp - 0x28 ]
clc
adcx rdi, [ rsp - 0x30 ]
adcx r10, r9
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx rbp, rax, rdi
adcx rcx, r8
mulx r15, rbp, rax
adcx r14, rbx
movzx r12, byte [ rsp - 0x20 ]
adox r12, r11
mov r9, 0xffffffff00000000 
mov rdx, rax
mulx r8, rax, r9
adcx r13, r12
mov rbx, 0xffffffff 
mulx r11, r12, rbx
mov rbx, -0x2 
inc rbx
adox rbp, r8
adox r12, r15
seto r15b
inc rbx
adox rdx, rdi
adox rax, r10
adox rbp, rcx
adox r12, r14
movzx rdx, r15b
lea rdx, [ rdx + r11 ]
adox rdx, r13
setc dil
seto r10b
mov rcx, rax
sub rcx, 0x00000001
mov r14, rbp
sbb r14, r9
movzx r8, r10b
movzx rdi, dil
lea r8, [ r8 + rdi ]
mov rdi, r12
mov r13, 0xffffffffffffffff 
sbb rdi, r13
mov r11, rdx
mov r15, 0xffffffff 
sbb r11, r15
sbb r8, 0x00000000
cmovc r14, rbp
cmovc rdi, r12
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], rdi
cmovc rcx, rax
mov [ r8 + 0x0 ], rcx
mov [ r8 + 0x8 ], r14
cmovc r11, rdx
mov [ r8 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4355
; seed 2134404167560402 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2059682 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=113, initial num_batches=31): 130080 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06315538029657006
; number reverted permutation / tried permutation: 68165 / 89975 =75.760%
; number reverted decision / tried decision: 57731 / 90024 =64.128%
; validated in 3.567s
