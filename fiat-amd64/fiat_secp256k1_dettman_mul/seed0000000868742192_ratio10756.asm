SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, r10
shrd rdx, r11, 52
mov r11, 0x1000003d10 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r11
xor rdx, rdx
adox rbp, r9
adox rbx, r12
mov rdx, [ rsi + 0x20 ]
mulx r12, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r11, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
adcx r9, r15
adcx r11, r12
add r9, rdi
adcx r8, r11
mov rdx, [ rax + 0x10 ]
mulx r15, r12, [ rsi + 0x8 ]
test al, al
adox rbp, r12
adox r15, rbx
mov rdx, 0xfffffffffffff 
and r10, rdx
mov rbx, 0x1000003d10 
mov rdx, r10
mulx rdi, r10, rbx
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, [ rax + 0x18 ]
adox rbp, r11
adox r12, r15
adcx r10, rbp
adcx r12, rdi
mov rdx, r10
shrd rdx, r12, 52
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, [ rax + 0x20 ]
xor rdx, rdx
adox r9, rdi
adox r11, r8
adcx r9, rbp
adcx r12, r11
xor r8, r8
adox r15, r9
adox r12, r8
adcx r13, r15
adcx r12, r14
mov rdx, [ rax + 0x8 ]
mulx rdi, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r11, rbp, [ rsi + 0x18 ]
test al, al
adox r14, rbp
adox r11, rdi
mov rdx, 0xfffffffffffff 
and r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, r9, [ rax + 0x18 ]
adox r14, r9
adox r15, r11
mov rdx, [ rsi + 0x8 ]
mulx rbp, rdi, [ rax + 0x20 ]
adcx r14, rdi
adcx rbp, r15
mov rdx, [ rax + 0x20 ]
mulx r9, r11, [ rsi + 0x18 ]
mov rdx, r13
shrd rdx, r12, 52
mov r15, 0x34 
bzhi rdi, r13, r15
mov r13, rdi
shr r13, 48
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, r8, [ rax + 0x18 ]
mov rdx, 0xffffffffffff 
and rdi, rdx
adox r12, r14
mov rdx, 0x0 
adox rbp, rdx
mov r14, r12
shrd r14, rbp, 52
mov rdx, [ rsi + 0x20 ]
mulx rbx, rbp, [ rax + 0x10 ]
xor rdx, rdx
adox rbp, r8
adox r15, rbx
mov rdx, [ rax + 0x20 ]
mulx rbx, r8, [ rsi + 0x10 ]
adcx rbp, r8
adcx rbx, r15
xor rdx, rdx
adox r14, rbp
adox rbx, rdx
mov r15, 0x34 
bzhi r8, r14, r15
bzhi rbp, r12, r15
mov rdx, [ rsi + 0x20 ]
mulx r15, r12, [ rax + 0x18 ]
shl rbp, 4
test al, al
adox r12, r11
adox r9, r15
lea rbp, [ rbp + r13 ]
mov rdx, 0x1000003d1 
mulx r13, r11, rbp
shrd r14, rbx, 52
add r14, r12
adc r9, 0x0
mov rbx, 0x34 
bzhi r15, r14, rbx
mov r12, 0x1000003d10 
mov rdx, r12
mulx rbp, r12, r15
mov rdx, [ rsi + 0x8 ]
mulx rbx, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r10
mulx r10, rdi, [ rax + 0x0 ]
adox rdi, r15
adox rbx, r10
test al, al
adox r11, rcx
adox r13, [ rsp - 0x48 ]
mov rdx, [ rax + 0x8 ]
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rbp
mulx rbp, r10, [ rax + 0x10 ]
mov rdx, r11
shrd rdx, r13, 52
xor r13, r13
adox rdi, r10
adox rbp, rbx
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mulx r13, r10, [ rsi + 0x8 ]
adcx r10, rcx
adcx r15, r13
add rbx, r10
adc r15, 0x0
mov rdx, 0x1000003d10 
mulx r13, rcx, r8
add rcx, rbx
adcx r15, r13
mov r8, rcx
shrd r8, r15, 52
xor r10, r10
adox r8, rdi
adox rbp, r10
adcx r12, r8
adcx rbp, [ rsp - 0x30 ]
mov rdi, 0xfffffffffffff 
mov rbx, r12
and rbx, rdi
shrd r12, rbp, 52
add r12, [ rsp - 0x38 ]
shrd r14, r9, 52
mulx r13, r9, r14
xor r15, r15
adox r9, r12
adox r13, r15
mov r10, r9
shrd r10, r13, 52
and r9, rdi
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], r9
mov [ r8 + 0x10 ], rbx
add r10, [ rsp - 0x40 ]
mov [ r8 + 0x20 ], r10
and r11, rdi
and rcx, rdi
mov [ r8 + 0x0 ], r11
mov [ r8 + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0756
; seed 0092380458526573 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1998535 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=332, initial num_batches=31): 165049 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08258499350774443
; number reverted permutation / tried permutation: 67485 / 90083 =74.914%
; number reverted decision / tried decision: 51444 / 89916 =57.213%
; validated in 0.699s
