SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 136
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbx
test al, al
adox rbp, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r13
mulx r13, rdi, rbx
adox rdi, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r14
mulx r14, r12, [ rsi + 0x8 ]
adcx r12, r10
adcx r8, r14
mov rdx, 0x0 
adox r13, rdx
mov r10, -0x3 
inc r10
adox rbx, rax
adox r15, r12
adox rbp, r8
adcx r11, r9
mov rdx, [ rsi + 0x0 ]
mulx rax, rbx, [ rsi + 0x8 ]
adox rdi, r11
mov rdx, 0x0 
adcx rcx, rdx
adox r13, rcx
mov rdx, [ rsi + 0x8 ]
mulx r14, r9, rdx
clc
adcx rbx, r15
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mulx r11, r15, rbx
seto r11b
inc r10
adox r9, rax
adox r12, r14
adcx r9, rbp
mov rdx, [ rsi + 0x18 ]
mulx rax, rbp, [ rsi + 0x8 ]
adcx r12, rdi
adox rbp, r8
adcx rbp, r13
mov rdx, [ rsi + 0x18 ]
mulx rcx, rdi, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rax, rdx
movzx r13, r11b
adcx r13, rax
mov rdx, [ rsi + 0x10 ]
mulx r14, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r8, [ rsi + 0x8 ]
inc r10
adox r8, [ rsp - 0x30 ]
adox r11, rax
adox rdi, r14
mov rdx, [ rsi + 0x8 ]
mulx rax, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r8
mulx r8, r11, [ rsi + 0x0 ]
mov rdx, 0x0 
adox rcx, rdx
mov [ rsp - 0x10 ], r11
mov r11, -0x3 
inc r11
adox r14, r8
adox r10, rax
adox rdi, [ rsp - 0x38 ]
mov rax, [ rsp - 0x48 ]
adox rax, rdx
mov r8, r15
mov r11, -0x3 
inc r11
adox r8, rbx
mov r8, 0xffffffff00000000 
mov rdx, r15
mulx rbx, r15, r8
mov r11, 0xffffffffffffffff 
mov [ rsp - 0x8 ], rax
mulx rax, r8, r11
adox r15, r9
setc r9b
clc
adcx r8, rbx
mov rbx, 0xffffffff 
mov [ rsp + 0x0 ], rdi
mulx rdi, r11, rbx
adcx r11, rax
adox r8, r12
mov rdx, 0x0 
adcx rdi, rdx
adox r11, rbp
adox rdi, r13
movzx r12, r9b
adox r12, rdx
xor rbp, rbp
adox r15, [ rsp - 0x40 ]
mov rdx, 0xffffffffffffffff 
mulx r13, r9, r15
mov rdx, rbx
mulx r13, rbx, r9
mov rax, r9
adcx rax, r15
adox r8, [ rsp - 0x18 ]
adox r11, [ rsp - 0x20 ]
mov rax, 0xffffffff00000000 
mov rdx, r9
mulx r15, r9, rax
adcx r9, r8
adox rdi, [ rsp - 0x28 ]
adox rcx, r12
mov r12, 0xffffffffffffffff 
mulx rbp, r8, r12
seto dl
mov rax, -0x2 
inc rax
adox r8, r15
adcx r8, r11
adox rbx, rbp
adcx rbx, rdi
seto r11b
inc rax
adox r9, [ rsp - 0x10 ]
movzx r15, r11b
lea r15, [ r15 + r13 ]
adox r14, r8
adcx r15, rcx
xchg rdx, r12
mulx rdi, r13, r9
mov rdi, 0xffffffff00000000 
mov rdx, r13
mulx rcx, r13, rdi
adox r10, rbx
mov rbp, 0xffffffffffffffff 
mulx r11, r8, rbp
movzx rbx, r12b
adcx rbx, rax
adox r15, [ rsp + 0x0 ]
adox rbx, [ rsp - 0x8 ]
mov r12, rdx
clc
adcx r12, r9
adcx r13, r14
seto r12b
mov r9, -0x3 
inc r9
adox r8, rcx
adcx r8, r10
mov r14, 0xffffffff 
mulx r10, rcx, r14
adox rcx, r11
adcx rcx, r15
adox r10, rax
adcx r10, rbx
movzx rdx, r12b
adc rdx, 0x0
mov r11, r13
sub r11, 0x00000001
mov r15, r8
sbb r15, rdi
mov r12, rcx
sbb r12, rbp
mov rbx, r10
sbb rbx, r14
sbb rdx, 0x00000000
cmovc r11, r13
cmovc rbx, r10
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r11
mov [ rdx + 0x18 ], rbx
cmovc r12, rcx
mov [ rdx + 0x10 ], r12
cmovc r15, r8
mov [ rdx + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4451
; seed 0977569334587504 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1334056 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=120, initial num_batches=31): 83749 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06277772447333545
; number reverted permutation / tried permutation: 67457 / 90078 =74.887%
; number reverted decision / tried decision: 58285 / 89921 =64.818%
; validated in 3.253s
