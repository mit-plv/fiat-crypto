SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r12
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r9
mulx r9, rbx, [ rax + 0x0 ]
xor rdx, rdx
adox rbx, r13
adox r14, r9
mov r13, rbp
shrd r13, r12, 52
mov rdx, [ rax + 0x10 ]
mulx r9, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, r12
adox r9, r14
mov rdx, [ rax + 0x0 ]
mulx r12, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
adcx r14, r10
adcx r11, r12
xor rdx, rdx
adox r14, r8
adox rcx, r11
adcx r14, r15
adcx rdi, rcx
mov r10, 0xfffffffffffff 
and rbp, r10
mov rdx, [ rsi + 0x0 ]
mulx r12, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, 0x1000003d10 
mulx r10, rcx, rbp
adox rcx, r14
adox rdi, r10
adcx rbx, r8
adcx r11, r9
mov r9, 0xfffffffffffff 
mov r14, rcx
and r14, r9
adox rbx, r15
adox r12, r11
shrd rcx, rdi, 52
mulx r15, rbp, r13
xor r13, r13
adox rcx, rbx
adox r12, r13
adcx rbp, rcx
adcx r12, r15
mov r8, rbp
and r8, r9
shrd rbp, r12, 52
mov r10, r8
shr r10, 48
mov rdx, [ rax + 0x8 ]
mulx r11, rdi, [ rsi + 0x20 ]
xor rdx, rdx
adox rdi, [ rsp - 0x10 ]
adox r11, [ rsp - 0x18 ]
adcx rdi, [ rsp + 0x10 ]
adcx r11, [ rsp + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx rbx, r13, [ rsi + 0x20 ]
xor rdx, rdx
adox rdi, [ rsp - 0x20 ]
adox r11, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x18 ]
mov rdx, 0x30 
bzhi r12, r8, rdx
adox r13, r15
adox rcx, rbx
test al, al
adox rbp, rdi
mov r8, 0x0 
adox r11, r8
mov rbx, rbp
and rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r15, rdi, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rax + 0x18 ]
shl rbx, 4
lea rbx, [ rbx + r10 ]
add r13, rdi
adcx r15, rcx
shrd rbp, r11, 52
add rbp, r13
adc r15, 0x0
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rax + 0x20 ]
mov rdx, 0x1000003d1 
mulx rdi, r11, rbx
mov rdx, [ rax + 0x0 ]
mulx r13, rbx, [ rsi + 0x8 ]
add r11, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
mov rdx, 0xfffffffffffff 
mov [ rsp + 0x18 ], r12
mov r12, r11
and r12, rdx
shrd r11, rdi, 52
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r14
mulx r14, rdi, [ rax + 0x0 ]
add rdi, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
xor rdx, rdx
adox r8, r10
adox rcx, r9
adcx rbx, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
mov r9, rbp
shrd r9, r15, 52
mov r15, 0xfffffffffffff 
and rbp, r15
adox r9, r8
adox rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r10, [ rax + 0x10 ]
adcx r11, rbx
adc r13, 0x0
mov rdx, 0x1000003d10 
mulx r15, rbx, rbp
test al, al
adox rbx, r11
adox r13, r15
mov rbp, 0x34 
bzhi r11, rbx, rbp
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r11
shrd rbx, r13, 52
xor r13, r13
adox rdi, r10
adox r8, r14
adcx rbx, rdi
adc r8, 0x0
mov [ r15 + 0x0 ], r12
bzhi r12, r9, rbp
mulx r10, r14, r12
adox r14, rbx
adox r8, r10
bzhi r11, r14, rbp
shrd r14, r8, 52
shrd r9, rcx, 52
add r14, [ rsp + 0x20 ]
mulx rdi, rcx, r9
xor rbx, rbx
adox rcx, r14
adox rdi, rbx
mov r13, rcx
shrd r13, rdi, 52
add r13, [ rsp + 0x18 ]
bzhi r12, rcx, rbp
mov [ r15 + 0x18 ], r12
mov [ r15 + 0x20 ], r13
mov [ r15 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0651
; seed 4318526519264859 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1445342 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=182, initial num_batches=31): 91038 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06298716843487562
; number reverted permutation / tried permutation: 70624 / 89934 =78.529%
; number reverted decision / tried decision: 52353 / 90065 =58.128%
; validated in 0.562s
