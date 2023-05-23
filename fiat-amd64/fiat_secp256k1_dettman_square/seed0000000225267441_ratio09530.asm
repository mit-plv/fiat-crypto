SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x0 ]
lea rdx, [r11 + r11]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbp
test al, al
adox r12, r9
adox rbx, r13
mov rdx, rax
shrd rdx, r10, 52
mov r10, 0xfffffffffffff 
and rax, r10
xchg rdx, rbp
mulx r13, r9, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r10, r15, rdx
adox r15, r9
adox r13, r10
mov rdx, [ rsi + 0x20 ]
mulx r10, r9, r11
adcx r15, r9
adcx r10, r13
mov rdx, 0x1000003d10 
mulx r9, r13, rax
test al, al
adox r13, r12
adox rbx, r9
mov r12, r13
shrd r12, rbx, 52
add r12, r15
adc r10, 0x0
mulx r15, rax, rbp
xor rbp, rbp
adox rax, r12
adox r10, r15
mov r9, 0x1 
shlx rbx, [ rsi + 0x10 ], r9
mov r12, rax
shrd r12, r10, 52
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, rbx
mov rdx, [ rsi + 0x20 ]
mulx r9, rbp, r14
xor rdx, rdx
adox r15, rbp
adox r9, r10
mov r14, 0x34 
bzhi r10, r13, r14
adox r12, r15
adox r9, rdx
bzhi r13, r12, r14
shrd r12, r9, 52
bzhi rbp, rax, r14
shl r13, 4
mov rax, 0xffffffffffff 
mov r15, rbp
and r15, rax
mov rdx, [ rsi + 0x20 ]
mulx r14, r9, rbx
adox rcx, r9
adox r14, r8
shr rbp, 48
mov rdx, [ rsi + 0x18 ]
mov r8, rdx
shl r8, 0x1
lea r13, [ r13 + rbp ]
xor rdx, rdx
adox r12, rcx
adox r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, rbx, rdx
mov rdx, r8
mulx rcx, r8, [ rsi + 0x20 ]
mov rbp, r12
shrd rbp, r14, 52
test al, al
adox rbp, r8
mov rdx, 0x0 
adox rcx, rdx
mov r14, 0x1000003d1 
mov rdx, r13
mulx r8, r13, r14
mov rdx, [ rsi + 0x8 ]
mulx rax, r14, rdx
adcx r13, rbx
adcx r9, r8
mov rdx, rbp
shrd rdx, rcx, 52
mov rbx, 0xfffffffffffff 
mov rcx, r13
and rcx, rbx
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, r11
adox r14, rbx
adox rdi, rax
mov rdx, [ rsi + 0x8 ]
mulx rbx, rax, r11
mov rdx, 0xfffffffffffff 
and r12, rdx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], rcx
mov rcx, 0x1000003d10 
mov rdx, rcx
mulx r11, rcx, r12
shrd r13, r9, 52
xor r9, r9
adox r13, rax
adox rbx, r9
adcx rcx, r13
adcx rbx, r11
mov rax, 0x34 
bzhi r12, rbp, rax
bzhi rbp, rcx, rax
shrd rcx, rbx, 52
mulx r13, r11, r12
add rcx, r14
adc rdi, 0x0
add r11, rcx
adcx rdi, r13
mov r14, r11
shrd r14, rdi, 52
bzhi rbx, r11, rax
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], rbx
lea r10, [ r10 + r14 ]
mulx rcx, r13, r8
adox r13, r10
adox rcx, r9
mov r8, r13
shrd r8, rcx, 52
lea r15, [ r15 + r8 ]
mov [ r12 + 0x20 ], r15
bzhi r11, r13, rax
mov [ r12 + 0x8 ], rbp
mov [ r12 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 0.9530
; seed 2351914705828844 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 696387 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=243, initial num_batches=31): 67405 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09679244443104193
; number reverted permutation / tried permutation: 74949 / 89949 =83.324%
; number reverted decision / tried decision: 60622 / 90050 =67.320%
; validated in 0.199s
