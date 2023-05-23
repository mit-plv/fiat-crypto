SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x0 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x8 ]
lea r11, [rax + rax]
mov rdx, [ rsi + 0x20 ]
mulx rcx, rax, rdx
mov rdx, 0xfffffffffffff 
mov r8, rax
and r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, r10
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r11
adox r13, r10
adox rbp, r14
mov rdx, 0x1000003d10 
mulx r14, r10, r8
adcx r10, r13
adcx rbp, r14
mov r8, r10
shrd r8, rbp, 52
mov rdx, [ rsi + 0x10 ]
mulx r14, r13, rdx
mov rdx, r11
mulx rbp, r11, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, r12
add r13, r11
adcx rbp, r14
shrd rax, rcx, 52
xor rdx, rdx
adox r13, rdi
adox rbx, rbp
adcx r8, r13
adc rbx, 0x0
mov rcx, 0x1000003d10 
mov rdx, rax
mulx r14, rax, rcx
mov rdx, r15
mulx r11, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox rax, r8
adox rbx, r14
mov rdi, rax
shrd rdi, rbx, 52
mov rbp, 0xfffffffffffff 
and rax, rbp
mov r13, 0x1 
shlx r8, [ rsi + 0x10 ], r13
mov rdx, r8
mulx r14, r8, [ rsi + 0x18 ]
adox r8, r15
adox r11, r14
adcx rdi, r8
adc r11, 0x0
mov r15, rdi
shrd r15, r11, 52
and rdi, rbp
shl rdi, 4
mov rbx, rax
shr rbx, 48
lea rdi, [ rdi + rbx ]
mulx r8, r14, [ rsi + 0x20 ]
mov rdx, 0x1000003d1 
mulx rbx, r11, rdi
xor rdi, rdi
adox r9, r14
adox r8, [ rsp - 0x48 ]
adcx r15, r9
adc r8, 0x0
mov r14, r15
shrd r14, r8, 52
and r15, rbp
mov rdx, rcx
mulx r9, rcx, r15
mov rdx, [ rsi + 0x0 ]
mulx r15, r8, rdx
adox r11, r8
adox r15, rbx
mov rdx, r11
shrd rdx, r15, 52
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r8, r12
mov rdx, 0xffffffffffff 
and rax, rdx
imul r13, [ rsi + 0x18 ], 0x2
xor rdx, rdx
adox rbx, r8
adox r15, rdx
adcx rcx, rbx
adcx r15, r9
mov rdi, rcx
shrd rdi, r15, 52
mov rdx, [ rsi + 0x8 ]
mulx r8, r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, rbx, r13
mov rdx, r12
mulx r13, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, rbx
adox r15, rdx
mov rbx, r14
shrd rbx, r15, 52
and r14, rbp
and r10, rbp
adox r9, r12
adox r13, r8
and r11, rbp
mov r8, 0x1000003d10 
mov rdx, r8
mulx r12, r8, r14
adox rdi, r9
mov r15, 0x0 
adox r13, r15
adcx r8, rdi
adcx r13, r12
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], r11
mov r9, r8
shrd r9, r13, 52
lea r10, [ r10 + r9 ]
and rcx, rbp
and r8, rbp
mov [ r14 + 0x8 ], rcx
mov [ r14 + 0x10 ], r8
mulx r12, r11, rbx
adox r11, r10
adox r12, r15
mov rbx, r11
shrd rbx, r12, 52
lea rax, [ rax + rbx ]
mov [ r14 + 0x20 ], rax
and r11, rbp
mov [ r14 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1625
; seed 2935319977919574 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 626361 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=450, initial num_batches=31): 78223 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.12488485074900896
; number reverted permutation / tried permutation: 76846 / 90260 =85.138%
; number reverted decision / tried decision: 67294 / 89739 =74.989%
; validated in 0.166s
