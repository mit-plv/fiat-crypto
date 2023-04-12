SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x0 ], 0x2
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, 0x34 
mov [ rsp - 0x78 ], rbp
bzhi rbp, rax, rdx
mov [ rsp - 0x70 ], r12
mov r12, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rsi + 0x8 ], r12
mov r12, 0x1000003d10 
mov rdx, rbp
mov [ rsp - 0x60 ], r14
mulx r14, rbp, r12
mov rdx, r13
mov [ rsp - 0x58 ], r15
mulx r15, r13, [ rsi + 0x10 ]
adox r13, rcx
adox r8, r15
mulx r15, rcx, [ rsi + 0x18 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, rdx
add rbp, r13
adcx r8, r14
add rdi, rcx
adcx r15, rbx
mov rdx, [ rsi + 0x20 ]
mulx r13, r14, r11
shrd rax, r10, 52
mov rdx, 0x1000003d10 
mulx rcx, r10, rax
test al, al
adox rdi, r14
adox r13, r15
mov rbx, rbp
shrd rbx, r8, 52
test al, al
adox rbx, rdi
mov r8, 0x0 
adox r13, r8
adcx r10, rbx
adcx r13, rcx
imul r15, [ rsi + 0x10 ], 0x2
mov rdx, r15
mulx r14, r15, [ rsi + 0x20 ]
mulx rcx, rax, [ rsi + 0x18 ]
mov rdi, 0xfffffffffffff 
mov rbx, r10
and rbx, rdi
mov rdx, [ rsi + 0x20 ]
mulx rdi, r8, r12
adox rax, r8
adox rdi, rcx
shrd r10, r13, 52
xor rdx, rdx
adox r10, rax
adox rdi, rdx
mov r12, 0xfffffffffffff 
mov r13, r10
and r13, r12
shrd r10, rdi, 52
shl r13, 4
xor rcx, rcx
adox r9, r15
adox r14, [ rsp - 0x48 ]
mov rdx, rbx
shr rdx, 48
lea r13, [ r13 + rdx ]
mov r15, 0x1000003d1 
mov rdx, r15
mulx r8, r15, r13
mov rdx, [ rsi + 0x0 ]
mulx rdi, rax, rdx
xor rdx, rdx
adox r15, rax
adox rdi, r8
adcx r10, r9
adc r14, 0x0
mov rcx, r15
shrd rcx, rdi, 52
mov r9, r10
and r9, r12
mov r13, 0x1000003d10 
mov rdx, r13
mulx r8, r13, r9
mov rdx, [ rsi + 0x8 ]
mulx rdi, rax, r11
adox rcx, rax
mov rdx, 0x0 
adox rdi, rdx
adcx r13, rcx
adcx rdi, r8
and r15, r12
mov rdx, [ rsi + 0x8 ]
mulx r8, r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, r11
adox r9, rax
adox rcx, r8
mov rdx, r13
and rdx, r12
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x8 ], rdx
imul r8, [ rsi + 0x18 ], 0x2
mov rdx, r8
mulx rax, r8, [ rsi + 0x20 ]
shrd r13, rdi, 52
shrd r10, r14, 52
and rbp, r12
adox r10, r8
mov r14, 0x0 
adox rax, r14
mov rdi, r10
shrd rdi, rax, 52
and r10, r12
mov rdx, 0x1000003d10 
mulx rax, r8, r10
adox r13, r9
adox rcx, r14
adcx r8, r13
adcx rcx, rax
mov r9, r8
and r9, r12
shrd r8, rcx, 52
mov r10, 0xffffffffffff 
and rbx, r10
mov [ r11 + 0x10 ], r9
lea rbp, [ rbp + r8 ]
mulx r13, rax, rdi
adox rax, rbp
adox r13, r14
mov rdi, rax
shrd rdi, r13, 52
lea rbx, [ rbx + rdi ]
and rax, r12
mov [ r11 + 0x18 ], rax
mov [ r11 + 0x20 ], rbx
mov [ r11 + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0399
; seed 2502860573317286 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1661810 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=247, initial num_batches=31): 131895 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07936827916548823
; number reverted permutation / tried permutation: 73528 / 89978 =81.718%
; number reverted decision / tried decision: 62986 / 90021 =69.968%
; validated in 0.342s
