SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
test al, al
adox r13, r10
adox r8, r14
mov rdx, [ rsi + 0x18 ]
mulx r14, r10, [ rsi + 0x0 ]
adox r10, r9
mov rdx, rbx
adcx rdx, rax
mov rdx, 0xffffffff00000000 
mulx r9, rax, rbx
adcx rax, r13
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp - 0x48 ], rdi
mulx rdi, r13, rbx
seto bl
mov rdx, -0x2 
inc rdx
adox rbp, r9
adox r13, r12
adcx rbp, r8
movzx r12, bl
lea r12, [ r12 + r14 ]
adcx r13, r10
mov rdx, [ rsi + 0x8 ]
mulx r14, r8, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rdi, rdx
mov rbx, -0x3 
inc rbx
adox r11, rax
adcx rdi, r12
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, rdx
mov rdx, 0xffffffffffffffff 
mulx r12, rax, r11
setc r12b
clc
adcx r10, rcx
adox r10, rbp
adcx r8, r9
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, [ rsi + 0x18 ]
adcx rcx, r14
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rsi + 0x10 ]
adox r8, r13
mov rdx, 0x0 
adcx rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r8
mulx r8, r13, [ rsi + 0x8 ]
clc
adcx r13, rbx
adox rcx, rdi
mov rdx, [ rsi + 0x18 ]
mulx rbx, rdi, [ rsi + 0x10 ]
movzx rdx, r12b
adox rdx, rbp
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r13
mulx r13, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rcx
mulx rcx, r12, [ rsi + 0x0 ]
seto dl
mov [ rsp - 0x18 ], r12
mov r12, -0x2 
inc r12
adox r14, rcx
adox r15, r9
adox rdi, [ rsp - 0x48 ]
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, rdx
adcx rbp, r8
adcx rcx, r13
mov rdx, 0xffffffff00000000 
mulx r13, r8, rax
mov rdx, rax
mov [ rsp - 0x10 ], rcx
setc cl
clc
adcx rdx, r11
adcx r8, r10
mov rdx, 0x0 
adox rbx, rdx
mov r11, 0xffffffffffffffff 
mov rdx, rax
mulx r10, rax, r11
mov r11, -0x2 
inc r11
adox rax, r13
movzx r13, cl
lea r13, [ r13 + r12 ]
mov r12, 0xffffffff 
mulx r11, rcx, r12
adox rcx, r10
mov rdx, 0x0 
adox r11, rdx
adcx rax, [ rsp - 0x38 ]
mov r10, -0x3 
inc r10
adox r8, [ rsp - 0x18 ]
adcx rcx, [ rsp - 0x20 ]
adox r14, rax
adox r15, rcx
adcx r11, [ rsp - 0x28 ]
movzx rax, r9b
adcx rax, rdx
adox rdi, r11
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx rcx, r9, r8
mulx r11, rcx, r9
mov r10, r9
clc
adcx r10, r8
adox rbx, rax
mov r10, 0xffffffff00000000 
mov rdx, r9
mulx r8, r9, r10
adcx r9, r14
mulx rax, r14, r12
seto dl
mov r12, -0x2 
inc r12
adox rcx, r8
adox r14, r11
adcx rcx, r15
adcx r14, rdi
mov r15, 0x0 
adox rax, r15
mov rdi, -0x3 
inc rdi
adox r9, [ rsp - 0x40 ]
adcx rax, rbx
adox rcx, [ rsp - 0x30 ]
movzx r11, dl
adcx r11, r15
mov rdx, 0xffffffffffffffff 
mulx r8, rbx, r9
adox rbp, r14
mov rdx, rbx
mulx rbx, r8, r10
adox rax, [ rsp - 0x10 ]
mov r14, rdx
clc
adcx r14, r9
adcx r8, rcx
mov r14, 0xffffffffffffffff 
mulx rcx, r9, r14
adox r13, r11
mov r11, 0xffffffff 
mulx rdi, r15, r11
seto dl
inc r12
adox r9, rbx
adcx r9, rbp
adox r15, rcx
adox rdi, r12
adcx r15, rax
adcx rdi, r13
movzx rbp, dl
adc rbp, 0x0
mov rbx, r8
sub rbx, 0x00000001
mov rax, r9
sbb rax, r10
mov rcx, r15
sbb rcx, r14
mov rdx, rdi
sbb rdx, r11
sbb rbp, 0x00000000
cmovc rcx, r15
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], rcx
cmovc rbx, r8
cmovc rdx, rdi
mov [ rbp + 0x18 ], rdx
mov [ rbp + 0x0 ], rbx
cmovc rax, r9
mov [ rbp + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4770
; seed 1369095885956818 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1827659 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=229, initial num_batches=31): 143131 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07831384300900769
; number reverted permutation / tried permutation: 66251 / 89590 =73.949%
; number reverted decision / tried decision: 57358 / 90409 =63.443%
; validated in 4.3s
