SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 176
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
mulx rax, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], rdi
mulx rdi, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], r14
mulx r14, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r11
mulx r11, r10, rdx
adox rbx, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], rbx
mulx rbx, rcx, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r12
mulx r12, rbx, rdx
adcx r8, r13
adox rbx, rbp
mov rdx, [ rsi + 0x0 ]
mulx r13, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r12
mulx r12, rbx, [ rsi + 0x8 ]
adcx rbx, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x10 ], r8
mov r8, -0x2 
inc r8
adox rbp, r11
adox r9, r13
adox r15, rbx
adcx rax, r12
mov r11, 0x0 
adox r14, r11
adc rdi, 0x0
mov r13, 0xffffffff00000000 
xchg rdx, rcx
mulx rbx, r12, r13
mov r8, rdx
xor r13, r13
adox r8, r10
mov r11, 0xffffffffffffffff 
mulx r10, r8, r11
adox r12, rbp
mov rbp, 0xffffffff 
mulx r11, r13, rbp
adcx r8, rbx
adox r8, r9
adcx r13, r10
adox r13, r15
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r12, [ rsp - 0x10 ]
adcx r8, [ rsp + 0x10 ]
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r15, r9, r12
mov r15, 0xffffffff00000000 
mov rdx, r9
mulx rbx, r9, r15
mov r10, 0xffffffffffffffff 
mulx r15, rbp, r10
adcx r13, [ rsp + 0x8 ]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x18 ], cl
mov [ rsp + 0x20 ], rdi
mulx rdi, rcx, [ rsi + 0x0 ]
adox r11, r14
adcx rax, r11
mov rdx, 0xffffffff 
mulx r11, r14, r10
seto dl
mov [ rsp + 0x28 ], rcx
mov rcx, -0x2 
inc rcx
adox rbp, rbx
setc bl
clc
adcx r10, r12
adox r14, r15
adcx r9, r8
adcx rbp, r13
mov r10, 0x0 
adox r11, r10
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mulx r15, r8, [ rsi + 0x8 ]
movzx rdx, r12b
dec r10
movzx rbx, bl
adox rbx, r10
adox rdx, [ rsp + 0x20 ]
adcx r14, rax
adcx r11, rdx
seto cl
inc r10
adox r8, rdi
adox r15, [ rsp - 0x28 ]
movzx r13, cl
adcx r13, r10
clc
adcx r9, [ rsp + 0x28 ]
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r12, rdi, r9
adcx r8, rbp
mov r12, 0xffffffff 
mov rdx, r12
mulx rbx, r12, rdi
mov rax, [ rsp - 0x30 ]
adox rax, [ rsp - 0x38 ]
adcx r15, r14
adcx rax, r11
mov rbp, [ rsp - 0x40 ]
adox rbp, r10
adcx rbp, r13
mov rcx, 0xffffffff00000000 
mov rdx, rcx
mulx r14, rcx, rdi
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r13, r11, rdi
mov rdx, -0x3 
inc rdx
adox rdi, r9
adox rcx, r8
setc dil
clc
adcx r11, r14
adcx r12, r13
adcx rbx, r10
clc
adcx rcx, [ rsp - 0x48 ]
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r8, r9, rcx
adox r11, r15
adox r12, rax
adox rbx, rbp
mulx r15, r8, r9
adcx r11, [ rsp - 0x20 ]
adcx r12, [ rsp - 0x18 ]
movzx rax, byte [ rsp + 0x18 ]
mov rbp, [ rsp + 0x0 ]
lea rax, [ rax + rbp ]
adcx rbx, [ rsp - 0x8 ]
mov rbp, r9
seto r14b
mov r13, -0x3 
inc r13
adox rbp, rcx
mov rbp, 0xffffffff00000000 
mov rdx, r9
mulx rcx, r9, rbp
adox r9, r11
movzx r11, r14b
movzx rdi, dil
lea r11, [ r11 + rdi ]
adcx rax, r11
mov rdi, 0xffffffff 
mulx r11, r14, rdi
setc dl
clc
adcx r8, rcx
adox r8, r12
adcx r14, r15
adox r14, rbx
adcx r11, r10
adox r11, rax
movzx r15, dl
adox r15, r10
mov r12, r9
sub r12, 0x00000001
mov rbx, r8
sbb rbx, rbp
mov rcx, r14
mov rdx, 0xffffffffffffffff 
sbb rcx, rdx
mov rax, r11
sbb rax, rdi
sbb r15, 0x00000000
cmovc rcx, r14
cmovc rax, r11
cmovc rbx, r8
cmovc r12, r9
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], r12
mov [ r15 + 0x10 ], rcx
mov [ r15 + 0x18 ], rax
mov [ r15 + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.2816
; seed 2242669282546835 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2057130 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 118382 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05754716522533821
; number reverted permutation / tried permutation: 76553 / 89877 =85.175%
; number reverted decision / tried decision: 47486 / 90122 =52.691%
; validated in 3.347s
