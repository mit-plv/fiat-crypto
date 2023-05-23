SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
imul rax, [ rsi + 0x10 ], 0x2
imul r10, [ rsi + 0x0 ], 0x2
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, r10
imul rdx, [ rsi + 0x8 ], 0x2
mulx r9, r8, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
xor r12, r12
adox rbx, r11
adox rcx, rbp
mulx rbp, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
adcx r14, r8
adcx r9, r15
mov rdx, 0xfffffffffffff 
mov r8, r12
and r8, rdx
mov r15, 0x1000003d10 
mov rdx, r8
mov [ rsp - 0x50 ], rdi
mulx rdi, r8, r15
shrd r12, r13, 52
add r8, rbx
adcx rcx, rdi
mov rbx, r8
shrd rbx, rcx, 52
mov rdx, r10
mulx r13, r10, [ rsi + 0x20 ]
test al, al
adox r14, r10
adox r13, r9
adcx rbx, r14
adc r13, 0x0
mov r9, 0xfffffffffffff 
and r8, r9
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, rax
mov rdx, r12
mulx r14, r12, r15
adox r12, rbx
adox r13, r14
mov rdx, r12
shrd rdx, r13, 52
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r13, r14, rax
xor rdx, rdx
adox rcx, r11
adox rbp, r10
adcx rbx, rcx
adc rbp, 0x0
and r12, r9
mov rax, r12
shr rax, 48
mov r11, rbx
and r11, r9
shl r11, 4
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, rdx
lea r11, [ r11 + rax ]
mov rdx, 0x1000003d1 
mulx r15, rax, r11
shrd rbx, rbp, 52
xor rbp, rbp
adox r10, r14
adox r13, rcx
adcx rbx, r10
adc r13, 0x0
imul r14, [ rsi + 0x18 ], 0x2
mov rdx, [ rsi + 0x20 ]
mulx r11, rcx, r14
mov rdx, 0x30 
bzhi r10, r12, rdx
mov r12, rbx
and r12, r9
mov rdx, [ rsi + 0x0 ]
mulx rbp, r14, rdx
shrd rbx, r13, 52
xor rdx, rdx
adox rbx, rcx
adox r11, rdx
adcx rax, r14
adcx rbp, r15
mov r15, rax
shrd r15, rbp, 52
mov rdx, rdi
mulx r13, rdi, [ rsi + 0x8 ]
and rax, r9
mov rcx, rbx
and rcx, r9
shrd rbx, r11, 52
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], rax
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx rax, rbp, rdx
mov rdx, 0x1000003d10 
mulx r14, r9, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r10
mulx r10, rbx, r11
test al, al
adox rbp, rbx
adox r10, rax
mov rdx, 0x1000003d10 
mulx rax, r11, r12
adcx r15, rdi
adc r13, 0x0
test al, al
adox r11, r15
adox r13, rax
mov r12, 0xfffffffffffff 
mov rdi, r11
and rdi, r12
shrd r11, r13, 52
xor rbx, rbx
adox r11, rbp
adox r10, rbx
mulx rax, rbp, rcx
adcx rbp, r11
adcx r10, rax
mov rcx, rbp
shrd rcx, r10, 52
lea r8, [ r8 + rcx ]
add r9, r8
adc r14, 0x0
mov r15, r9
and r15, r12
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], r15
shrd r9, r14, 52
and rbp, r12
mov [ r13 + 0x10 ], rbp
add r9, [ rsp - 0x48 ]
mov [ r13 + 0x8 ], rdi
mov [ r13 + 0x20 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0113
; seed 1369983670599547 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1490246 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=457, initial num_batches=31): 158183 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10614556254470739
; number reverted permutation / tried permutation: 74865 / 89767 =83.399%
; number reverted decision / tried decision: 64192 / 90232 =71.141%
; validated in 0.444s
