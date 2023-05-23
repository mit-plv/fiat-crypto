SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 232
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], r10
mulx r10, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r11
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r10
mulx r10, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, 0xfffffffffffff 
mov [ rsp + 0x28 ], r12
mov r12, r11
and r12, rdx
adox r8, r15
adox rdi, rcx
adcx r9, r14
adcx r13, rbx
xor rbx, rbx
adox r9, rbp
adox r13, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbp, [ rax + 0x0 ]
adcx rbp, [ rsp + 0x20 ]
adcx rcx, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], rdi
mulx rdi, rbx, [ rax + 0x18 ]
test al, al
adox r9, rbx
adox rdi, r13
adcx rbp, r15
adcx r14, rcx
mov rdx, 0x1000003d10 
mulx rcx, r13, r12
xor r12, r12
adox rbp, [ rsp + 0x10 ]
adox r14, [ rsp + 0x8 ]
adcx r13, r9
adcx rdi, rcx
xor r15, r15
adox rbp, [ rsp - 0x20 ]
adox r14, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mulx rbx, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, [ rax + 0x10 ]
adcx r12, r9
adcx rcx, rbx
add r12, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, rbx, [ rax + 0x20 ]
add r12, rbx
adcx r9, rcx
mov rdx, 0x34 
bzhi rcx, r13, rdx
shrd r11, r10, 52
mov r10, 0x1000003d10 
mov rdx, r11
mulx rbx, r11, r10
shrd r13, rdi, 52
add r13, rbp
adc r14, 0x0
mov rdx, [ rsi + 0x10 ]
mulx rbp, rdi, [ rax + 0x20 ]
add r11, r13
adcx r14, rbx
mov rdx, 0x34 
bzhi rbx, r11, rdx
mov r13, rbx
shr r13, 48
shrd r11, r14, 52
xor r14, r14
adox r11, r12
adox r9, r14
bzhi r15, r11, rdx
shl r15, 4
shrd r11, r9, 52
mov r12, [ rsp + 0x0 ]
test al, al
adox r12, [ rsp - 0x10 ]
mov r9, [ rsp - 0x8 ]
adox r9, [ rsp - 0x18 ]
adcx r12, rdi
adcx rbp, r9
lea r15, [ r15 + r13 ]
mov rdx, [ rax + 0x18 ]
mulx r13, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, [ rax + 0x20 ]
mov rdx, 0x1000003d1 
mov [ rsp + 0x38 ], rcx
mulx rcx, r10, r15
test al, al
adox rdi, r9
adox r14, r13
adcx r10, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
mov r15, 0x34 
bzhi r13, r10, r15
mov rdx, [ rax + 0x0 ]
mulx r15, r9, [ rsi + 0x8 ]
shrd r10, rcx, 52
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x40 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
test al, al
adox r11, r12
mov rdx, 0x0 
adox rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], r8
mulx r8, r12, [ rsi + 0x0 ]
mov rdx, 0x34 
mov [ rsp + 0x50 ], rcx
bzhi rcx, r11, rdx
mov rdx, 0x1000003d10 
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], rdi
mulx rdi, r14, rcx
adox r9, r12
adox r8, r15
test al, al
adox r10, r9
mov r15, 0x0 
adox r8, r15
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x0 ], r13
adcx r14, r10
adcx r8, rdi
shrd r11, rbp, 52
add r11, [ rsp + 0x60 ]
mov r13, [ rsp + 0x58 ]
adc r13, 0x0
mov rbp, 0xfffffffffffff 
mov rcx, r11
and rcx, rbp
mov rdi, [ rsp + 0x40 ]
adox rdi, [ rsp + 0x50 ]
mov r9, [ rsp + 0x30 ]
adox r9, [ rsp + 0x48 ]
mov r10, r14
shrd r10, r8, 52
mulx r15, r8, rcx
xor rcx, rcx
adox r10, rdi
adox r9, rcx
adcx r8, r10
adcx r9, r15
mov rdi, r8
and rdi, rbp
shrd r11, r13, 52
mulx r15, r13, r11
mov [ r12 + 0x10 ], rdi
shrd r8, r9, 52
add r8, [ rsp + 0x38 ]
xor r10, r10
adox r13, r8
adox r15, r10
mov rcx, 0x30 
bzhi r9, rbx, rcx
mov rbx, r13
shrd rbx, r15, 52
lea r9, [ r9 + rbx ]
and r13, rbp
mov [ r12 + 0x18 ], r13
and r14, rbp
mov [ r12 + 0x8 ], r14
mov [ r12 + 0x20 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 232
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9368
; seed 1555829256233820 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2317157 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=123, initial num_batches=31): 130787 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05644287374571511
; number reverted permutation / tried permutation: 67655 / 89932 =75.229%
; number reverted decision / tried decision: 31560 / 90067 =35.041%
; validated in 0.618s
