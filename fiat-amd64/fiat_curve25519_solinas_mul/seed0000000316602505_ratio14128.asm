SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], rcx
mulx rcx, rdi, [ rsi + 0x18 ]
test al, al
adox rdi, r9
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r14
mulx r14, r9, [ rsi + 0x0 ]
adox r10, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r9
mulx r9, r14, [ rax + 0x8 ]
adcx r14, rdi
mov rdx, 0x0 
adox r8, rdx
adcx rcx, r10
mov rdi, rdx
adcx rdi, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r10, [ rsi + 0x10 ]
adc r8, 0x0
xor rdx, rdx
adox rbp, rbx
adox r12, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r10
mulx r10, r14, [ rsi + 0x18 ]
adox rbx, rcx
adox r14, rdi
mov rdx, [ rax + 0x8 ]
mulx rdi, rcx, [ rsi + 0x8 ]
adcx rcx, rbp
adcx r15, r12
adcx r9, rbx
mov rdx, [ rax + 0x18 ]
mulx r12, rbp, [ rsi + 0x18 ]
adcx r11, r14
mov rdx, 0x0 
mov rbx, rdx
adox rbx, r8
mov rdx, [ rax + 0x0 ]
mulx r14, r8, [ rsi + 0x0 ]
mov rdx, 0x0 
mov [ rsp - 0x8 ], r8
mov r8, rdx
adcx r8, rbx
adox r12, rdx
adcx r12, rdx
test al, al
adox r13, r14
adox rcx, [ rsp - 0x28 ]
adox rdi, r15
adox r9, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x20 ]
adox r11, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x48 ]
adcx r11, [ rsp - 0x18 ]
mov r15, 0x26 
mov rdx, r15
mulx rbx, r15, r11
adox rbp, r8
adcx r10, rbp
seto r14b
mov r8, -0x2 
inc r8
adox r15, r13
mov r13, 0x0 
movzx r14, r14b
lea r12, [ r12 + r13 ]
lea r12, [ r12 + r14 ]
mulx r14, r11, r10
adox r11, rcx
adcx r12, r13
mulx rbp, rcx, r12
adox rcx, rdi
mulx r10, rdi, r9
adox rbp, r13
add rdi, [ rsp - 0x8 ]
adcx r10, r15
adcx rbx, r11
adcx r14, rcx
adc rbp, 0x0
mulx r15, r9, rbp
test al, al
adox r9, rdi
mov r15, r13
adox r15, r10
mov r11, r13
adox r11, rbx
mov r12, r13
adox r12, r14
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r15
mov rdi, r13
cmovo rdi, rdx
adcx r9, rdi
mov [ rcx + 0x0 ], r9
mov [ rcx + 0x10 ], r11
mov [ rcx + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4128
; seed 0044619729941062 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1187399 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=361, initial num_batches=31): 132522 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11160696615038417
; number reverted permutation / tried permutation: 57135 / 90028 =63.464%
; number reverted decision / tried decision: 45960 / 89971 =51.083%
; validated in 0.721s
