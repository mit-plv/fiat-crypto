SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x18 ]
lea rdx, [r11 + r11]
mov r11, 0x1 
shlx rcx, [ rsi + 0x8 ], r11
mov r8, [ rsi + 0x0 ]
lea r9, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r11, rdx
mov rdx, 0x34 
mov [ rsp - 0x78 ], rbp
bzhi rbp, r11, rdx
mov rdx, r9
mov [ rsp - 0x70 ], r12
mulx r12, r9, [ rsi + 0x18 ]
xchg rdx, rcx
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
shrd r11, rbx, 52
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r12
mulx r12, r11, r8
mov rdx, r8
mov [ rsp - 0x30 ], r9
mulx r9, r8, [ rsi + 0x18 ]
add r8, r13
adcx r14, r9
test al, al
adox rax, r11
adox r12, r10
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, rbx
adcx r15, r10
adcx r13, rdi
mov rdx, 0x1000003d10 
mulx r11, rdi, rbp
mov rdx, [ rsi + 0x10 ]
mulx r9, rbp, rbx
add rbp, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
test al, al
adox rdi, rbp
adox r9, r11
mov rdx, rdi
shrd rdx, r9, 52
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, rcx
mov rdx, 0xfffffffffffff 
and rdi, rdx
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x20 ]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r11
mulx r11, rdi, rdx
adox r15, rcx
adox rbp, r13
adcx rbx, r15
adc rbp, 0x0
mov rdx, 0x1000003d10 
mulx rcx, r13, [ rsp - 0x40 ]
test al, al
adox r13, rbx
adox rbp, rcx
mov r15, r13
shrd r15, rbp, 52
mov rbx, 0x34 
bzhi rcx, r13, rbx
mov r13, rcx
shr r13, 48
xor rbp, rbp
adox r15, r8
adox r14, rbp
bzhi r8, r15, rbx
shl r8, 4
lea r8, [ r8 + r13 ]
shrd r15, r14, 52
mov r13, 0x1000003d1 
mov rdx, r13
mulx r14, r13, r8
xor r8, r8
adox r15, rax
adox r12, r8
mov rdx, [ rsp - 0x48 ]
mulx rax, rbp, [ rsi + 0x20 ]
bzhi rdx, r15, rbx
shrd r15, r12, 52
add r15, rbp
adc rax, 0x0
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, rdx
bzhi rdx, r15, rbx
adox r13, rbp
adox r8, r14
shrd r15, rax, 52
mov r14, 0x1000003d10 
mulx rbp, rax, r14
mov rdx, r14
mulx rbx, r14, r15
mov r15, 0xfffffffffffff 
mov rdx, r13
and rdx, r15
adox rdi, r10
adox r11, [ rsp - 0x20 ]
shrd r13, r8, 52
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r8, r9
xor rdx, rdx
adox r13, r8
adox r15, rdx
mov r9, 0x1000003d10 
mov rdx, r9
mulx r8, r9, r12
adcx r9, r13
adcx r15, r8
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x0 ], r10
mov r10, r9
shrd r10, r15, 52
add r10, rdi
adc r11, 0x0
test al, al
adox rax, r10
adox r11, rbp
mov rbp, rax
shrd rbp, r11, 52
mov rdi, 0xfffffffffffff 
and r9, rdi
mov [ r12 + 0x8 ], r9
add rbp, [ rsp - 0x28 ]
test al, al
adox r14, rbp
mov r13, 0x0 
adox rbx, r13
mov r8, 0x30 
bzhi r15, rcx, r8
mov rcx, r14
and rcx, rdi
mov [ r12 + 0x18 ], rcx
shrd r14, rbx, 52
lea r15, [ r15 + r14 ]
and rax, rdi
mov [ r12 + 0x20 ], r15
mov [ r12 + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 0.9814
; seed 4430124589542693 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5806 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=244, initial num_batches=31): 484 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08336203926972098
; number reverted permutation / tried permutation: 406 / 498 =81.526%
; number reverted decision / tried decision: 330 / 501 =65.868%
; validated in 0.268s
