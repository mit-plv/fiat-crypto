SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, r10
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x78 ], rbp
mov rbp, rcx
and rbp, rdx
mov [ rsp - 0x70 ], r12
mov r12, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
lea r13, [r12 + r12]
adox r9, rax
adox r11, rbx
mov rdx, r13
mulx r13, r12, [ rsi + 0x20 ]
adcx r9, r12
adcx r13, r11
mulx rbx, rax, [ rsi + 0x8 ]
mulx r12, r11, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, 0x1000003d10 
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rax
mulx rax, rbx, rbp
xor rbp, rbp
adox r15, r11
adox r12, rdi
adcx rbx, r15
adcx r12, rax
mov r11, rbx
shrd r11, r12, 52
shrd rcx, r8, 52
mulx rdi, r8, rcx
xor rax, rax
adox r11, r9
adox r13, rax
mov rbp, 0xfffffffffffff 
and rbx, rbp
adox r8, r11
adox r13, rdi
mov r9, [ rsi + 0x10 ]
mov r15, r9
shl r15, 0x1
mov rdx, r15
mulx r15, r9, [ rsi + 0x18 ]
mov r12, r8
and r12, rbp
mulx rdi, rcx, [ rsi + 0x20 ]
shrd r8, r13, 52
mov r11, r12
shr r11, 48
mov rdx, r10
mulx r13, r10, [ rsi + 0x20 ]
test al, al
adox r9, r10
adox r13, r15
adcx r8, r9
adc r13, 0x0
mov rdx, r8
shrd rdx, r13, 52
and r8, rbp
shl r8, 4
lea r8, [ r8 + r11 ]
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, r11, rdx
xor rdx, rdx
adox r11, rcx
adox rdi, r10
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, rdx
mov rdx, 0x1000003d1 
mulx r13, r9, r8
adcx r9, rax
adcx rcx, r13
add r15, r11
adc rdi, 0x0
mov r8, r15
and r8, rbp
shrd r15, rdi, 52
mov r10, 0x1000003d10 
mov rdx, r10
mulx r11, r10, r8
mov rax, r9
and rax, rbp
mov r13, [ rsi + 0x18 ]
lea rdi, [r13 + r13]
mov rdx, rdi
mulx r13, rdi, [ rsi + 0x20 ]
shrd r9, rcx, 52
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], rax
xor r8, r8
adox r15, rdi
adox r13, r8
adcx r9, [ rsp - 0x40 ]
mov rax, [ rsp - 0x48 ]
adc rax, 0x0
add r10, r9
adcx rax, r11
mov r11, r15
shrd r11, r13, 52
mov rdx, r14
mulx rdi, r14, [ rsi + 0x10 ]
mov rdx, r10
and rdx, rbp
mov [ rcx + 0x8 ], rdx
shrd r10, rax, 52
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, rdx
add r13, r14
adcx rdi, r9
add r10, r13
adc rdi, 0x0
and r15, rbp
mov rdx, 0x1000003d10 
mulx r14, rax, r15
adox rax, r10
adox rdi, r14
mov r9, rax
shrd r9, rdi, 52
and rax, rbp
mov [ rcx + 0x10 ], rax
mulx r10, r13, r11
lea rbx, [ rbx + r9 ]
adox r13, rbx
adox r10, r8
mov r11, r13
and r11, rbp
mov [ rcx + 0x18 ], r11
shrd r13, r10, 52
mov r15, 0xffffffffffff 
and r12, r15
lea r12, [ r12 + r13 ]
mov [ rcx + 0x20 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1428
; seed 0869701317201844 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 626326 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=450, initial num_batches=31): 79063 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.12623298410093145
; number reverted permutation / tried permutation: 75689 / 90057 =84.046%
; number reverted decision / tried decision: 66956 / 89942 =74.444%
; validated in 0.168s
