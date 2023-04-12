SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], r9
mulx r9, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r12
mulx r12, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rdi
mulx rdi, r9, [ rax + 0x10 ]
test al, al
adox r13, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, rbx, [ rax + 0x8 ]
adcx rbx, r13
adox r15, r8
adcx r14, r15
mov rdx, [ rax + 0x18 ]
mulx r13, r8, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r13, rdx
mov r15, -0x3 
inc r15
adox r10, r12
adox r11, rbx
mov r12, rdx
adcx r12, r13
mov rdx, [ rax + 0x18 ]
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
adox rcx, r14
adox r15, r12
mov rdx, 0x0 
adcx r13, rdx
mov r14, rdx
adox r14, r13
clc
adcx rbp, r10
adcx r9, r11
adcx rdi, rcx
mov rdx, [ rax + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
adcx r15, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r12, [ rax + 0x0 ]
seto dl
mov r13, -0x2 
inc r13
adox r12, r11
adox rcx, rbp
adox r9, [ rsp - 0x30 ]
mov rbp, 0x0 
mov r11, rbp
adcx r11, r14
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mulx r13, rbp, [ rax + 0x18 ]
setc dl
clc
adcx r12, [ rsp - 0x28 ]
adcx rcx, [ rsp - 0x40 ]
adox r8, rdi
adox r15, [ rsp - 0x10 ]
adox rbp, r11
adcx r9, [ rsp - 0x48 ]
adcx r8, [ rsp - 0x18 ]
adcx r15, [ rsp - 0x38 ]
adcx rbx, rbp
mov rdi, 0x26 
xchg rdx, rdi
mulx rbp, r11, rbx
movzx rbx, r14b
lea rbx, [ rbx + r13 ]
mov r14, 0x0 
movzx rdi, dil
lea rbx, [ rbx + r14 ]
lea rbx, [ rbx + rdi ]
adox rbx, r14
adcx rbx, r14
mulx r13, rdi, r15
test al, al
adox rdi, r12
adox r11, rcx
mulx rcx, r12, r8
adcx r12, r10
adcx rcx, rdi
mulx r8, r10, rbx
adox r10, r9
adox r8, r14
adcx r13, r11
adcx rbp, r10
adc r8, 0x0
mulx r15, r9, r8
add r9, r12
mov r15, r14
adcx r15, rcx
mov rbx, r14
adcx rbx, r13
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], rbx
mov r11, r14
adcx r11, rbp
mov r12, r14
cmovc r12, rdx
mov rcx, -0x3 
inc rcx
adox r9, r12
mov [ rdi + 0x8 ], r15
mov [ rdi + 0x18 ], r11
mov [ rdi + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5529
; seed 1684845414858954 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1232203 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=121, initial num_batches=31): 94697 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07685178497374215
; number reverted permutation / tried permutation: 64433 / 90071 =71.536%
; number reverted decision / tried decision: 30704 / 89928 =34.143%
; validated in 0.57s
