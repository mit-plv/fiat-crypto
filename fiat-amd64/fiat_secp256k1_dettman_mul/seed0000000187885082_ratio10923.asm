SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, r13
shrd rdx, r14, 52
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
test al, al
adox rbp, r15
adox rdi, r12
adcx rbp, r10
adcx r11, rdi
mov rdx, [ rax + 0x18 ]
mulx r12, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mulx rdi, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox rbp, r10
adox r12, r11
mov rdx, [ rsi + 0x18 ]
mulx r10, r11, [ rax + 0x0 ]
adcx r11, r15
adcx rdi, r10
mov rdx, 0xfffffffffffff 
and r13, rdx
mov rdx, [ rax + 0x20 ]
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rax + 0x18 ]
adox r11, r9
adox rbx, rdi
adcx r11, rcx
adcx r8, rbx
mov rdx, 0x1000003d10 
mulx rdi, r9, r13
test al, al
adox r9, r11
adox r8, rdi
mov r13, r9
shrd r13, r8, 52
test al, al
adox rbp, r15
adox r10, r12
adcx r13, rbp
adc r10, 0x0
mulx r15, r12, r14
add r12, r13
adcx r10, r15
mov r14, 0x34 
bzhi rcx, r9, r14
bzhi rbx, r12, r14
shrd r12, r10, 52
mov rdx, [ rsi + 0x20 ]
mulx rdi, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r9, [ rax + 0x10 ]
add r11, r9
adcx r8, rdi
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x18 ]
xor rdx, rdx
adox r11, rbp
adox r13, r8
mov rdx, [ rsi + 0x8 ]
mulx r10, r15, [ rax + 0x20 ]
adcx r11, r15
adcx r10, r13
xor rdx, rdx
adox r12, r11
adox r10, rdx
mov rdi, 0x30 
bzhi r9, rbx, rdi
bzhi r8, r12, r14
shrd r12, r10, 52
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx rdi, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r9
mulx r9, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
shr rbx, 48
shl r8, 4
xor rdx, rdx
adox r14, r10
adox rdi, r9
adcx r14, rbp
adcx r13, rdi
lea r8, [ r8 + rbx ]
add r12, r14
adc r13, 0x0
mov rbp, 0x34 
bzhi r10, r12, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbx, r9, [ rax + 0x0 ]
adox rcx, r15
adox r11, [ rsp - 0x18 ]
mov rdx, 0x1000003d10 
mulx rdi, r15, r10
shrd r12, r13, 52
mov rdx, [ rax + 0x0 ]
mulx r13, r14, [ rsi + 0x0 ]
add r12, rcx
adc r11, 0x0
mov rdx, 0x1000003d1 
mulx rcx, r10, r8
test al, al
adox r10, r14
adox r13, rcx
mov rdx, [ rax + 0x8 ]
mulx r14, r8, [ rsi + 0x0 ]
mov rdx, r8
adcx rdx, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
mov rcx, r10
shrd rcx, r13, 52
test al, al
adox rcx, rdx
mov r13, 0x0 
adox r14, r13
mov rdx, [ rax + 0x8 ]
mulx r13, r8, [ rsi + 0x8 ]
bzhi rdx, r12, rbp
adox r15, rcx
adox r14, rdi
mov rdi, 0x1000003d10 
mulx rbp, rcx, rdi
mov rdx, 0x34 
bzhi rdi, r15, rdx
adox r9, r8
adox r13, rbx
xor rbx, rbx
adox r9, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
shrd r15, r14, 52
test al, al
adox r15, r9
adox r13, rbx
adcx rcx, r15
adcx r13, rbp
mov r8, rcx
shrd r8, r13, 52
add r8, [ rsp - 0x20 ]
shrd r12, r11, 52
mov r11, 0x1000003d10 
mov rdx, r12
mulx r14, r12, r11
xor rbp, rbp
adox r12, r8
adox r14, rbp
mov rbx, 0x34 
bzhi r9, r12, rbx
shrd r12, r14, 52
add r12, [ rsp - 0x28 ]
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x20 ], r12
bzhi r13, r10, rbx
bzhi r10, rcx, rbx
mov [ r15 + 0x8 ], rdi
mov [ r15 + 0x10 ], r10
mov [ r15 + 0x0 ], r13
mov [ r15 + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0923
; seed 3062198780316455 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2242656 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=179, initial num_batches=31): 141861 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06325580026539959
; number reverted permutation / tried permutation: 70698 / 90171 =78.404%
; number reverted decision / tried decision: 52413 / 89828 =58.348%
; validated in 0.519s
