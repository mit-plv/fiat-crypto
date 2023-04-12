SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov rdx, rdi
test al, al
adox rdx, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r13
mulx r13, r10, [ rax + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r10
mulx r10, r13, rdi
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r10
mulx r10, r15, [ rsi + 0x10 ]
adcx rbp, r11
adcx rcx, r12
mov rdx, 0xffffffff00000000 
mulx r12, r11, rdi
adcx r9, r8
adox r11, rbp
mov rdx, [ rax + 0x8 ]
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r8, r14
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r10
mulx r10, r14, [ rsi + 0x8 ]
adcx r14, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
adcx rbp, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], rbp
mulx rbp, r10, rdi
mov rdi, 0x0 
adcx r15, rdi
clc
adcx r10, r12
adcx r13, rbp
mov r12, [ rsp - 0x10 ]
adcx r12, rdi
adox r10, rcx
adox r13, r9
adox r12, rbx
clc
adcx r11, [ rsp - 0x38 ]
mulx r9, rcx, r11
mov r9, rcx
seto bl
mov rbp, -0x3 
inc rbp
adox r9, r11
adcx r8, r10
adcx r14, r13
mov r9, 0xffffffff00000000 
mov rdx, rcx
mulx r10, rcx, r9
adcx r12, [ rsp + 0x8 ]
movzx r13, bl
adcx r13, r15
mov r15, 0xffffffffffffffff 
mulx r11, rbx, r15
setc bpl
clc
adcx rbx, r10
mov r10, 0xffffffff 
mulx r15, rdi, r10
adcx rdi, r11
adox rcx, r8
mov rdx, 0x0 
adcx r15, rdx
adox rbx, r14
adox rdi, r12
adox r15, r13
movzx r8, bpl
adox r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x0 ]
test al, al
adox r13, [ rsp - 0x40 ]
adcx rbp, rcx
mov rdx, 0xffffffffffffffff 
mulx rcx, r11, rbp
adox r14, [ rsp - 0x48 ]
adox r12, [ rsp + 0x0 ]
mov rdx, r11
mulx rcx, r11, r9
adcx r13, rbx
mulx r9, rbx, r10
adcx r14, rdi
adcx r12, r15
mov rdi, [ rsp - 0x8 ]
mov r15, 0x0 
adox rdi, r15
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x10 ], r9
mulx r9, r10, r15
mov r15, -0x2 
inc r15
adox r10, rcx
adox rbx, r9
adcx rdi, r8
setc r8b
clc
adcx rdx, rbp
adcx r11, r13
adcx r10, r14
adcx rbx, r12
mov rdx, [ rsp + 0x10 ]
mov rbp, 0x0 
adox rdx, rbp
adcx rdx, rdi
movzx rcx, r8b
adc rcx, 0x0
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mulx r12, r14, [ rsi + 0x18 ]
xor rdx, rdx
adox r14, r11
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r9, rbp, r14
mulx r8, r9, rbp
mov rdx, [ rax + 0x10 ]
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x18 ], r8
mulx r8, r15, rbp
adcx r12, [ rsp - 0x18 ]
adox r12, r10
adcx rdi, [ rsp - 0x30 ]
adox rdi, rbx
adcx r11, [ rsp - 0x20 ]
mov r10, [ rsp - 0x28 ]
mov rbx, 0x0 
adcx r10, rbx
mov rbx, 0xffffffff00000000 
mov rdx, rbp
mov [ rsp + 0x20 ], r8
mulx r8, rbp, rbx
adox r11, r13
clc
adcx rdx, r14
adcx rbp, r12
adox r10, rcx
seto dl
mov r13, -0x2 
inc r13
adox r9, r8
adox r15, [ rsp + 0x18 ]
adcx r9, rdi
adcx r15, r11
mov rcx, [ rsp + 0x20 ]
mov r14, 0x0 
adox rcx, r14
adcx rcx, r10
setc r12b
mov rdi, rbp
sub rdi, 0x00000001
mov r8, r9
sbb r8, rbx
mov r11, r15
mov r10, 0xffffffffffffffff 
sbb r11, r10
movzx r14, r12b
movzx rdx, dl
lea r14, [ r14 + rdx ]
mov rdx, rcx
mov r12, 0xffffffff 
sbb rdx, r12
sbb r14, 0x00000000
cmovc r8, r9
cmovc rdi, rbp
cmovc r11, r15
cmovc rdx, rcx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rdx
mov [ r14 + 0x0 ], rdi
mov [ r14 + 0x8 ], r8
mov [ r14 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5313
; seed 2375514950689492 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1294459 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=129, initial num_batches=31): 86749 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06701564128334694
; number reverted permutation / tried permutation: 66781 / 89899 =74.284%
; number reverted decision / tried decision: 46227 / 90100 =51.306%
; validated in 3.047s
