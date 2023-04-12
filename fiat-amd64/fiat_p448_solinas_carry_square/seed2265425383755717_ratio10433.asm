SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 464
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, 0x1 
shlx rdx, [ rsi + 0x38 ], r11
mulx r8, rcx, [ rsi + 0x8 ]
imul r9, [ rsi + 0x8 ], 0x2
mov [ rsp - 0x80 ], rbx
mulx rbx, r11, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0x1 
mov [ rsp - 0x60 ], r14
shlx r14, [ rsi + 0x18 ], rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, rbp
mov rdx, rbp
mov [ rsp - 0x38 ], r8
mulx r8, rbp, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r8
mov r8, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rbp
lea rbp, [r8 + r8]
mov r8, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], rcx
lea rcx, [r8 + r8]
mov [ rsp - 0x18 ], r12
mulx r12, r8, [ rsi + 0x30 ]
mov [ rsp - 0x10 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], rax
mulx rax, r10, rcx
mov rdx, rcx
mov [ rsp + 0x8 ], rdi
mulx rdi, rcx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], rdi
mulx rdi, rcx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], rbx
imul rbx, [ rsi + 0x20 ], 0x2
mov [ rsp + 0x48 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], r14
mulx r14, r11, rbx
mov rdx, rbx
mov [ rsp + 0x60 ], r14
mulx r14, rbx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r14
mov [ rsp + 0x70 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], r14
mulx r14, rbx, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], rcx
mulx rcx, rdi, r9
xor rdx, rdx
adox r10, rbx
adox r14, rax
mov rdx, rbp
mulx r9, rbp, [ rsi + 0x8 ]
xchg rdx, r15
mulx rbx, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rbx
mov [ rsp + 0xa8 ], rax
mulx rax, rbx, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], rcx
mulx rcx, r13, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], rcx
mulx rcx, r11, r15
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp + 0xc0 ], rcx
mulx rcx, r15, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], r13
mulx r13, r11, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], r11
mulx r11, r13, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rdi
mov rdi, r8
add rdi, r8
mov [ rsp + 0xf0 ], rax
mov rax, r12
adcx rax, r12
test al, al
adox rdi, r13
mov [ rsp + 0xf8 ], rbx
mov rbx, r11
adox rbx, rax
adcx r8, r13
adcx r11, r12
test al, al
adox r8, [ rsp + 0x98 ]
adox r11, [ rsp + 0x90 ]
mov r12, r10
adcx r12, [ rsp + 0x88 ]
mov r13, r14
adcx r13, [ rsp + 0x80 ]
mov [ rsp + 0x100 ], rbx
mulx rbx, rax, [ rsi + 0x0 ]
add r12, r15
adcx rcx, r13
add r10, rbp
adcx r9, r14
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, rbp, [ rsp + 0x58 ]
mov rdx, [ rsp + 0x30 ]
mov r13, rdx
test al, al
adox r13, [ rsp + 0x50 ]
mov [ rsp + 0x108 ], rbx
mov rbx, [ rsp + 0x8 ]
mov [ rsp + 0x110 ], rax
mov rax, rbx
adox rax, [ rsp + 0x38 ]
adcx r8, [ rsp + 0xf8 ]
adcx r11, [ rsp + 0xf0 ]
test al, al
adox r10, rbp
adox r15, r9
xchg rdx, r14
mulx rbp, r9, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffff 
mov [ rsp + 0x118 ], rdi
mov rdi, r10
and rdi, rdx
shrd r10, r15, 56
add r8, [ rsp + 0xe8 ]
adcx r11, [ rsp + 0xb0 ]
mov r15, r13
add r15, r14
adcx rbx, rax
test al, al
adox r15, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x38 ]
adcx r12, [ rsp + 0x48 ]
adcx rcx, [ rsp + 0x40 ]
xor r14, r14
adox r13, [ rsp + 0x0 ]
adox rax, [ rsp - 0x8 ]
adcx r13, r9
mov rdx, rbp
adcx rdx, rax
add r13, [ rsp + 0x18 ]
adcx rdx, [ rsp + 0x10 ]
xor rax, rax
adox r12, [ rsp - 0x10 ]
adox rcx, [ rsp - 0x18 ]
adcx r15, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x8 ]
mov r14, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x120 ], rdi
mulx rdi, rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], r8
mulx r8, r11, rdx
mov rdx, rax
add rdx, rax
mov [ rsp + 0x138 ], r10
mov r10, rdi
adcx r10, rdi
add r13, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x38 ]
test al, al
adox r15, r9
adox rbp, rbx
mov r9, 0x38 
bzhi rbx, r12, r9
adox rdx, r11
mov r9, r8
adox r9, r10
xor r10, r10
adox rax, r11
adox r8, rdi
adcx rax, [ rsp + 0xa8 ]
adcx r8, [ rsp + 0xa0 ]
mov rdi, [ rsp + 0x118 ]
xor r11, r11
adox rdi, [ rsp + 0x98 ]
mov r10, [ rsp + 0x100 ]
adox r10, [ rsp + 0x90 ]
adcx rdx, [ rsp + 0xa8 ]
adcx r9, [ rsp + 0xa0 ]
add rdx, [ rsp - 0x28 ]
adcx r9, [ rsp - 0x30 ]
test al, al
adox r13, [ rsp - 0x40 ]
adox r14, [ rsp - 0x48 ]
shrd r12, rcx, 56
mov rcx, r12
mov [ rsp + 0x140 ], rbx
xor rbx, rbx
adox rcx, r13
adox r14, rbx
mov r11, rcx
shrd r11, r14, 56
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, rdx
add r13, r14
adcx rbx, r9
add r15, [ rsp + 0x18 ]
adcx rbp, [ rsp + 0x10 ]
xor rdx, rdx
adox r13, [ rsp + 0x78 ]
adox rbx, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, rdx
adcx r15, r9
adcx r14, rbp
mov rdx, [ rsi + 0x8 ]
mulx r9, rbp, [ rsp + 0x58 ]
xor rdx, rdx
adox r15, [ rsp - 0x20 ]
adox r14, [ rsp - 0x38 ]
adcx r15, rbp
adcx r9, r14
test al, al
adox r15, [ rsp + 0x70 ]
adox r9, [ rsp + 0x68 ]
adcx r15, [ rsp + 0x138 ]
adc r9, 0x0
xor rbp, rbp
adox r13, [ rsp + 0xe0 ]
adox rbx, [ rsp + 0xd8 ]
mov rdx, [ rsp + 0x58 ]
mulx rbp, r14, [ rsi + 0x10 ]
adcx r12, r15
adc r9, 0x0
add rdi, [ rsp + 0xf8 ]
adcx r10, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x148 ], rbx
mulx rbx, r15, rdx
mov rdx, r12
shrd rdx, r9, 56
test al, al
adox rdi, r14
adox rbp, r10
mov r14, r11
adcx r14, [ rsp + 0x130 ]
mov r9, [ rsp + 0x128 ]
adc r9, 0x0
mov r11, r14
shrd r11, r9, 56
test al, al
adox rdi, [ rsp + 0xd0 ]
adox rbp, [ rsp + 0xb8 ]
adcx rax, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x30 ]
add rdi, [ rsp + 0x110 ]
adcx rbp, [ rsp + 0x108 ]
add rax, r15
adcx rbx, r8
xor r10, r10
adox rax, [ rsp + 0xc8 ]
adox rbx, [ rsp + 0xc0 ]
adcx rax, r11
adc rbx, 0x0
mov r15, rax
shrd r15, rbx, 56
mov r9, 0x38 
bzhi r11, rax, r9
bzhi r8, r12, r9
add r15, [ rsp + 0x120 ]
bzhi r12, r15, r9
bzhi rax, r14, r9
adox rdi, rdx
adox rbp, r10
xor rdx, rdx
adox r13, [ rsp + 0x28 ]
mov r10, [ rsp + 0x20 ]
adox r10, [ rsp + 0x148 ]
mov r14, rdi
shrd r14, rbp, 56
add r13, r14
adc r10, 0x0
mov rbx, r13
shrd rbx, r10, 56
bzhi rbp, r13, r9
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], r12
mov [ r14 + 0x30 ], rbp
add rbx, [ rsp + 0x140 ]
bzhi r12, rcx, r9
bzhi rcx, rbx, r9
mov [ r14 + 0x38 ], rcx
shr rbx, 56
lea r8, [ r8 + rbx ]
lea r12, [ r12 + rbx ]
shr r15, 56
lea r15, [ r15 + r8 ]
bzhi r13, r12, r9
bzhi r10, r15, r9
mov [ r14 + 0x0 ], r13
shr r15, 56
shr r12, 56
lea r12, [ r12 + rax ]
mov [ r14 + 0x10 ], r11
bzhi r11, rdi, r9
lea r15, [ r15 + r11 ]
mov [ r14 + 0x28 ], r15
mov [ r14 + 0x8 ], r12
mov [ r14 + 0x20 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 464
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0433
; seed 2265425383755717 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 34226 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=95, initial num_batches=31): 1022 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.02986034009232747
; number reverted permutation / tried permutation: 338 / 472 =71.610%
; number reverted decision / tried decision: 348 / 527 =66.034%
; validated in 2.532s
