SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
imul rax, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rax
mov rdx, r10
shrd rdx, r11, 52
xchg rdx, rax
mulx r11, r9, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov rbx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rbx
shl rbp, 0x1
mov rbx, 0x34 
mov [ rsp - 0x70 ], r12
bzhi r12, r10, rbx
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, 0x1000003d10 
mov [ rsp - 0x58 ], r15
mulx rbx, r15, rax
adox r13, r9
adox r11, r14
mov rdx, [ rsi + 0x10 ]
mulx r9, rax, rbp
mov rdx, rbp
mulx r14, rbp, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov rdi, 0x1000003d10 
xchg rdx, r12
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], rax
mulx rax, r9, rdi
xor rdx, rdx
adox rcx, rbp
adox r14, r8
adcx r9, rcx
adcx r14, rax
mov rdx, r12
mulx r8, r12, [ rsi + 0x20 ]
mov rbp, r9
shrd rbp, r14, 52
test al, al
adox r13, r12
adox r8, r11
adcx rbp, r13
adc r8, 0x0
xor r11, r11
adox r15, rbp
adox r8, rbx
mov rbx, r15
shrd rbx, r8, 52
mov rax, 0xfffffffffffff 
and r15, rax
mov rcx, r15
shr rcx, 48
xchg rdx, r10
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov r13, rdx
shl r13, 0x1
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, rdx
mov rdx, r13
mulx r11, r13, [ rsi + 0x18 ]
xor rdi, rdi
adox r13, r14
adox r12, r11
adcx rbx, r13
adc r12, 0x0
mov r14, rbx
and r14, rax
shl r14, 4
mulx r13, r11, [ rsi + 0x20 ]
shrd rbx, r12, 52
lea r14, [ r14 + rcx ]
mov rcx, 0x1000003d1 
mov rdx, rcx
mulx r12, rcx, r14
test al, al
adox rcx, rbp
adox r8, r12
mov rbp, rcx
and rbp, rax
shrd rcx, r8, 52
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, rdx
test al, al
adox r14, r11
adox r13, r12
adcx rbx, r14
adc r13, 0x0
imul rdx, [ rsi + 0x18 ], 0x2
mov r11, rbx
shrd r11, r13, 52
mulx r12, r8, [ rsi + 0x20 ]
add r11, r8
adc r12, 0x0
mov r14, r11
shrd r14, r12, 52
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rbp
and r11, rax
and rbx, rax
mov rdx, r10
mulx rbp, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, rdx
mov rdx, 0x1000003d10 
mulx rax, rdi, rbx
adox rcx, r10
mov rbx, 0x0 
adox rbp, rbx
adcx rdi, rcx
adcx rbp, rax
mov r10, 0xfffffffffffff 
mov rax, rdi
and rax, r10
shrd rdi, rbp, 52
mov [ r13 + 0x8 ], rax
add r8, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
add rdi, r8
adc r12, 0x0
mulx rbp, rcx, r11
add rcx, rdi
adcx r12, rbp
and r9, r10
mov r11, 0x30 
bzhi rax, r15, r11
mulx r8, r15, r14
mov r14, rcx
shrd r14, r12, 52
lea r9, [ r9 + r14 ]
xor rdi, rdi
adox r15, r9
adox r8, rdi
mov rbx, r15
shrd rbx, r8, 52
and r15, r10
mov [ r13 + 0x18 ], r15
and rcx, r10
lea rax, [ rax + rbx ]
mov [ r13 + 0x10 ], rcx
mov [ r13 + 0x20 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0317
; seed 3157305429317542 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 940169 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=278, initial num_batches=31): 88670 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09431283099102396
; number reverted permutation / tried permutation: 76875 / 90143 =85.281%
; number reverted decision / tried decision: 54819 / 89856 =61.008%
; validated in 0.254s
