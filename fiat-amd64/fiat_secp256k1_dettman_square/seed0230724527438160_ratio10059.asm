SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x0 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r11
imul rdx, [ rsi + 0x8 ], 0x2
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rbp
mulx rbp, rcx, [ rsi + 0x20 ]
xor rdx, rdx
adox rax, r12
adox r13, r10
mov rdx, [ rsi + 0x20 ]
mulx r12, r10, rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x30 ], r13
mov r13, r10
and r13, rdx
mov rdx, r11
mov [ rsp - 0x28 ], rax
mulx rax, r11, [ rsi + 0x18 ]
adox rdi, r11
adox rax, r8
shrd r10, r12, 52
xor r8, r8
adox r9, r14
adox r15, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, r11, rbx
adcx r9, r11
adcx r8, r15
mov rdx, rbx
mulx r15, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox r14, rcx
adox rbp, r12
mov rcx, 0x1000003d10 
mov rdx, rcx
mulx r12, rcx, r13
adcx rcx, rdi
adcx rax, r12
mov r13, rcx
shrd r13, rax, 52
xor rdi, rdi
adox r13, r9
adox r8, rdi
mulx r9, r11, r10
adcx r11, r13
adcx r8, r9
mov rdx, [ rsi + 0x18 ]
mulx r12, r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx r13, rax, [ rsp - 0x38 ]
mov rdx, r11
shrd rdx, r8, 52
add r10, rax
adcx r13, r12
xor r9, r9
adox rdx, r14
adox rbp, r9
mov rdi, 0xfffffffffffff 
mov r14, rdx
and r14, rdi
shrd rdx, rbp, 52
test al, al
adox rdx, r10
adox r13, r9
and r11, rdi
mov r8, rdx
shrd r8, r13, 52
mov r12, r11
shr r12, 48
mov rax, 0x30 
bzhi r10, r11, rax
shl r14, 4
and rdx, rdi
mov rbp, 0x1000003d10 
mulx r11, r13, rbp
mov rdx, [ rsi + 0x18 ]
lea r9, [rdx + rdx]
lea r14, [ r14 + r12 ]
mov rdx, 0x1000003d1 
mulx rax, r12, r14
mov rdx, r9
mulx r14, r9, [ rsi + 0x20 ]
adox r8, r9
mov rdx, 0x0 
adox r14, rdx
adcx r12, [ rsp - 0x40 ]
adcx rax, [ rsp - 0x48 ]
mov r9, r12
and r9, rdi
shrd r12, rax, 52
test al, al
adox r12, rbx
adox r15, rdx
adcx r13, r12
adcx r15, r11
mov rbx, r8
shrd rbx, r14, 52
and r8, rdi
mov rdx, rbp
mulx r11, rbp, r8
mulx rax, r14, rbx
mov r12, r13
and r12, rdi
shrd r13, r15, 52
and rcx, rdi
adox r13, [ rsp - 0x28 ]
mov r15, [ rsp - 0x30 ]
mov rbx, 0x0 
adox r15, rbx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], r9
adcx rbp, r13
adcx r15, r11
mov r9, rbp
shrd r9, r15, 52
lea rcx, [ rcx + r9 ]
add r14, rcx
adc rax, 0x0
mov r11, r14
and r11, rdi
and rbp, rdi
mov [ r8 + 0x8 ], r12
shrd r14, rax, 52
mov [ r8 + 0x10 ], rbp
mov [ r8 + 0x18 ], r11
lea r10, [ r10 + r14 ]
mov [ r8 + 0x20 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0059
; seed 0230724527438160 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9260 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=465, initial num_batches=31): 935 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1009719222462203
; number reverted permutation / tried permutation: 377 / 480 =78.542%
; number reverted decision / tried decision: 348 / 519 =67.052%
; validated in 0.448s
