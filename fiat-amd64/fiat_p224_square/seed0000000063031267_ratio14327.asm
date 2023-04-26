SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 176
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rbx
mulx rbx, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r12
adox rbp, r9
adox rax, rbx
mov rdx, [ rsi + 0x0 ]
mulx r12, r9, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r10
mulx r10, rbx, rdx
adcx rbx, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r12, [ rsi + 0x18 ]
adcx r11, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r11
mulx r11, r10, [ rsi + 0x18 ]
adcx r12, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
adc rbx, 0x0
add rcx, r11
adcx r14, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r11, rdx
adcx r11, r15
adc r10, 0x0
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], r10
mulx r10, r15, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r11
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
test al, al
adox r10, r13
adox r11, [ rsp - 0x38 ]
adox r14, [ rsp - 0x40 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x10 ], r14
mulx r14, r13, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, r15
adcx r11, r14
mov r14, 0x0 
adox rcx, r14
mov r14, 0xffffffff 
mov rdx, r15
mov [ rsp + 0x28 ], rcx
mulx rcx, r15, r14
adcx r15, r10
adc rcx, 0x0
xor r10, r10
adox rdx, rdi
adox r13, r8
adox r11, rbp
adox r15, rax
adcx r9, r13
adox rcx, [ rsp - 0x30 ]
mov rdx, 0xffffffffffffffff 
mulx r8, rdi, r9
adcx r11, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x20 ]
adcx r12, rcx
mulx rbp, r8, rdi
mov rax, rdi
setc r13b
clc
adcx rax, r9
mov rax, 0xffffffff00000000 
mov rdx, rdi
mulx r9, rdi, rax
adcx rdi, r11
mulx r11, rcx, r14
movzx rdx, r13b
adox rdx, rbx
seto bl
mov r13, -0x3 
inc r13
adox r8, r9
adcx r8, r15
adox rcx, rbp
adox r11, r10
mov r15, -0x3 
inc r15
adox rdi, [ rsp - 0x48 ]
mov r15, 0xffffffffffffffff 
xchg rdx, r15
mulx r9, rbp, rdi
adcx rcx, r12
mov rdx, rbp
mulx rbp, r9, rax
mov r12, rdx
setc r13b
clc
adcx r12, rdi
setc r12b
clc
mov rdi, -0x1 
movzx r13, r13b
adcx r13, rdi
adcx r15, r11
movzx r11, bl
adcx r11, r10
adox r8, [ rsp + 0x20 ]
adox rcx, [ rsp + 0x18 ]
adox r15, [ rsp + 0x10 ]
mov rbx, 0xffffffffffffffff 
mulx r10, r13, rbx
clc
adcx r13, rbp
mulx rdi, rbp, r14
adcx rbp, r10
mov rdx, 0x0 
adcx rdi, rdx
clc
mov r10, -0x1 
movzx r12, r12b
adcx r12, r10
adcx r8, r9
adcx r13, rcx
adcx rbp, r15
adox r11, [ rsp + 0x28 ]
adcx rdi, r11
setc r9b
clc
adcx r8, [ rsp - 0x18 ]
movzx r12, r9b
adox r12, rdx
adcx r13, [ rsp + 0x8 ]
mov rdx, rbx
mulx rcx, rbx, r8
mov rdx, rbx
mulx rbx, rcx, rax
adcx rbp, [ rsp + 0x0 ]
mov r15, rdx
inc r10
adox r15, r8
adox rcx, r13
adcx rdi, [ rsp - 0x8 ]
mov r15, 0xffffffffffffffff 
mulx r9, r11, r15
adcx r12, [ rsp - 0x10 ]
mulx r13, r8, r14
setc dl
clc
adcx r11, rbx
adox r11, rbp
adcx r8, r9
adox r8, rdi
adcx r13, r10
adox r13, r12
movzx rbx, dl
adox rbx, r10
mov rbp, rcx
sub rbp, 0x00000001
mov rdi, r11
sbb rdi, rax
mov r9, r8
sbb r9, r15
mov rdx, r13
sbb rdx, r14
sbb rbx, 0x00000000
cmovc rbp, rcx
cmovc r9, r8
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], r9
cmovc rdx, r13
mov [ rbx + 0x18 ], rdx
mov [ rbx + 0x0 ], rbp
cmovc rdi, r11
mov [ rbx + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4327
; seed 3407210376043203 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1427274 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 83960 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.058825425251213155
; number reverted permutation / tried permutation: 67393 / 89888 =74.974%
; number reverted decision / tried decision: 58931 / 90111 =65.398%
; validated in 3.356s
