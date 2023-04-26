SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 392
imul rax, [ rsi + 0x38 ], 0x2
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, rax
mov rdx, [ rsi + 0x30 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
imul rdx, [ rsi + 0x28 ], 0x2
xchg rdx, rcx
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov r14, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov r15, r14
shl r15, 0x1
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rdi
mulx rdi, rbx, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r9
mulx r9, r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], r14
mulx r14, r9, r15
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r9
mulx r9, r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], r9
mulx r9, r8, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r9
mulx r9, r14, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r9
mov [ rsp + 0x30 ], r14
mulx r14, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], rdi
mulx rdi, r8, rax
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], rdi
mulx rdi, rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r13
mulx r13, r8, rbp
mov rdx, rbx
mov [ rsp + 0x68 ], r13
xor r13, r13
adox rdx, r10
mov [ rsp + 0x70 ], r8
mov r8, r11
adox r8, rdi
mov [ rsp + 0x78 ], r12
mov r12, rdx
adcx r12, rbx
adcx rdi, r8
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], rdi
mulx rdi, r13, rcx
add rbx, r9
mov rdx, r14
adcx rdx, r8
xor r8, r8
adox r12, r10
adox r11, [ rsp + 0x80 ]
adcx r12, r9
adcx r14, r11
xor r10, r10
adox r12, r13
mov r8, rdi
adox r8, r14
adcx r12, [ rsp + 0x78 ]
adcx r8, [ rsp + 0x60 ]
add rbx, r13
adcx rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r9, r15
mov rdx, [ rsi + 0x10 ]
lea r15, [rdx + rdx]
xor rdx, rdx
adox rbx, [ rsp + 0x78 ]
adox rdi, [ rsp + 0x60 ]
mov rdx, rbp
mulx rbp, r10, [ rsi + 0x18 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rbp
mulx rbp, r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r10
mov [ rsp + 0x98 ], rdi
mulx rdi, r10, r11
adcx r12, r14
adcx rbp, r8
xor rdx, rdx
adox r12, [ rsp + 0x58 ]
adox rbp, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, r15
adcx r12, r9
adcx r13, rbp
xor rdx, rdx
adox r10, [ rsp + 0x48 ]
adox rdi, [ rsp + 0x40 ]
mov r9, r10
adcx r9, r11
adcx r8, rdi
mov rdx, [ rsi + 0x0 ]
mulx rbp, r14, r15
xor rdx, rdx
adox r9, [ rsp + 0x38 ]
adox r8, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mulx r11, r15, rdx
mov rdx, r9
shrd rdx, r8, 56
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rbp
mov [ rsp + 0xa8 ], r14
mulx r14, rbp, rcx
mov rdx, 0x38 
mov [ rsp + 0xb0 ], r8
bzhi r8, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r8
mulx r8, r9, [ rsp + 0x18 ]
adox r10, r9
adox r8, rdi
xor rdx, rdx
adox r10, rbp
adox r14, r8
mov rdi, r15
adcx rdi, [ rsp + 0x10 ]
mov rbp, r11
adcx rbp, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ rsp + 0x18 ]
xor rdx, rdx
adox r12, r9
adox r8, r13
mov rdx, [ rsi + 0x18 ]
mulx r9, r13, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], rdi
mulx rdi, rbp, rax
adcx r10, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x28 ]
mov rdx, [ rsp + 0x10 ]
mov [ rsp + 0xd0 ], r9
mov r9, rdx
test al, al
adox r9, rdx
mov [ rsp + 0xd8 ], r13
mov r13, [ rsp + 0x8 ]
adox r13, r13
adcx r10, rbp
adcx rdi, r14
mov rdx, r10
shrd rdx, rdi, 56
xor rbp, rbp
adox rbx, [ rsp + 0x58 ]
mov r14, [ rsp + 0x50 ]
adox r14, [ rsp + 0x98 ]
adcx r12, [ rsp + 0xb0 ]
adc r8, 0x0
mov rdi, rdx
add rdi, r12
adc r8, 0x0
mov r12, rdi
shrd r12, r8, 56
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r12
mulx r12, rbp, rdx
test al, al
adox rbx, rbp
adox r12, r14
adcx r8, rbx
adc r12, 0x0
test al, al
adox r9, r15
adox r11, r13
mov rdx, [ rsi + 0x30 ]
mulx r13, r15, rax
adcx r9, [ rsp + 0x70 ]
adcx r11, [ rsp + 0x68 ]
add r9, [ rsp + 0xd8 ]
adcx r11, [ rsp + 0xd0 ]
mov rdx, rax
mulx r14, rax, [ rsi + 0x10 ]
mov rdx, r15
xor rbp, rbp
adox rdx, r15
mov rbx, r13
adox rbx, r13
adcx rdx, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x28 ]
mov [ rsp + 0xe8 ], r12
xor r12, r12
adox rdx, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x88 ]
adcx r15, [ rsp + 0x30 ]
adcx r13, [ rsp + 0x28 ]
add r9, [ rsp - 0x18 ]
adcx r11, [ rsp - 0x20 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r8
mulx r8, r12, [ rsp + 0x18 ]
mov rdx, [ rsp + 0x18 ]
mov [ rsp + 0xf8 ], r13
mov [ rsp + 0x100 ], r15
mulx r15, r13, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r13
adox r15, r11
adcx rbp, rax
mov r11, r14
adcx r11, rbx
xor rbx, rbx
adox rbp, [ rsp - 0x8 ]
adox r11, [ rsp - 0x10 ]
adcx rbp, r12
adcx r8, r11
mov rdx, rcx
mulx r12, rcx, [ rsi + 0x8 ]
mulx r11, r13, [ rsi + 0x0 ]
test al, al
adox r9, rcx
adox r12, r15
adcx rbp, r13
adcx r11, r8
xor rdx, rdx
adox rbp, [ rsp + 0xe0 ]
adox r11, rdx
adcx r9, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
mov rbx, rbp
shrd rbx, r11, 56
add r9, rbx
adc r12, 0x0
mov r15, 0x38 
bzhi r8, rbp, r15
mov rcx, r9
shrd rcx, r12, 56
mov r13, [ rsp + 0x70 ]
mov rbp, r13
add rbp, [ rsp + 0xc8 ]
mov r11, [ rsp + 0x68 ]
adcx r11, [ rsp + 0xc0 ]
xor r13, r13
adox rbp, [ rsp + 0xd8 ]
adox r11, [ rsp + 0xd0 ]
adcx rbp, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
bzhi rdx, r10, r15
lea rcx, [ rcx + rdx ]
mov r10, rcx
shr r10, 56
bzhi rbx, r9, r15
mov r9, [ rsp + 0x100 ]
adox r9, [ rsp + 0x90 ]
mov r12, [ rsp + 0xf8 ]
adox r12, [ rsp + 0x88 ]
xor rdx, rdx
adox r9, rax
adox r14, r12
mov r13, [ rsi + 0x8 ]
lea rax, [r13 + r13]
mov rdx, [ rsi + 0x0 ]
mulx r12, r13, rax
adcx r9, r13
adcx r12, r14
bzhi rdx, [ rsp + 0xf0 ], r15
mov r14, [ rsp + 0xf0 ]
mov rax, [ rsp + 0xe8 ]
shrd r14, rax, 56
lea rdx, [ rdx + r10 ]
test al, al
adox r9, r14
mov rax, 0x0 
adox r12, rax
bzhi r13, r9, r15
mov r14, rdx
shr r14, 56
bzhi rax, rdx, r15
adox rbp, [ rsp + 0xa8 ]
adox r11, [ rsp + 0xa0 ]
shrd r9, r12, 56
bzhi rdx, rcx, r15
adox rbp, r9
mov rcx, 0x0 
adox r11, rcx
mov r12, rbp
shrd r12, r11, 56
add r12, [ rsp + 0xb8 ]
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x38 ], rdx
mov rdx, r12
shr rdx, 56
bzhi r11, rdi, r15
lea r11, [ r11 + r10 ]
lea rdx, [ rdx + r11 ]
bzhi rdi, rdx, r15
shr rdx, 56
lea rdx, [ rdx + r8 ]
mov [ r9 + 0x0 ], rax
lea r14, [ r14 + r13 ]
mov [ r9 + 0x8 ], r14
mov [ r9 + 0x30 ], rbx
bzhi r8, rbp, r15
mov [ r9 + 0x10 ], r8
bzhi r10, r12, r15
mov [ r9 + 0x20 ], rdi
mov [ r9 + 0x28 ], rdx
mov [ r9 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 392
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.0963
; seed 3522430298922862 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3127102 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=138, initial num_batches=31): 106306 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03399505356716858
; number reverted permutation / tried permutation: 64760 / 90092 =71.882%
; number reverted decision / tried decision: 59128 / 89907 =65.766%
; validated in 2.04s
