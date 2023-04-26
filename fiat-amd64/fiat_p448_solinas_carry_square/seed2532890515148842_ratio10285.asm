SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 488
mov rdx, [ rsi + 0x38 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x20 ]
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, 0x1 
mov [ rsp - 0x78 ], rbp
shlx rbp, [ rsi + 0x10 ], rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, r12
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp - 0x38 ], rdi
mov rdi, rax
test al, al
adox rdi, rax
mov [ rsp - 0x30 ], r15
mov r15, r10
adox r15, r10
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rsi + 0x18 ]
xchg rdx, r8
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r13
imul r13, [ rsi + 0x30 ], 0x2
mov [ rsp + 0x10 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r9
mulx r9, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], rcx
mulx rcx, r11, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r11
mulx r11, rcx, r12
xor rdx, rdx
adox rdi, rbx
mov [ rsp + 0x48 ], r11
mov r11, r9
adox r11, r15
mov rdx, r13
mulx r15, r13, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], r15
mulx r15, rcx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r13
mulx r13, rcx, rdx
mov rdx, r14
mov [ rsp + 0x78 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x88 ], r14
mov [ rsp + 0x90 ], rcx
mulx rcx, r14, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], r14
mulx r14, rcx, r15
adcx rax, rbx
adcx r9, r10
mov rdx, r8
mulx r10, r8, [ rsi + 0x10 ]
xor rbx, rbx
adox rax, rcx
mov [ rsp + 0xa8 ], r10
mov r10, r14
adox r10, r9
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, 0x1 
mov [ rsp + 0xb0 ], rbx
shlx rbx, [ rsi + 0x38 ], rdx
imul rdx, [ rsi + 0x8 ], 0x2
mov [ rsp + 0xb8 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r10
mulx r10, r8, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], rax
mov [ rsp + 0xd8 ], rbp
mulx rbp, rax, rbx
mov rdx, r9
mov [ rsp + 0xe0 ], r11
mulx r11, r9, [ rsi + 0x0 ]
add r8, rax
adcx rbp, r10
test al, al
adox rdi, rcx
adox r14, [ rsp + 0xe0 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, r12
mov rdx, [ rsi + 0x8 ]
mulx rax, r12, [ rsp + 0xd8 ]
mov rdx, r8
adcx rdx, r12
adcx rax, rbp
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r14
mov [ rsp + 0xf0 ], rdi
mulx rdi, r14, r15
xor rdx, rdx
adox r12, rcx
adox r10, rax
mov rdx, [ rsi + 0x10 ]
mulx rcx, r15, r13
mov rdx, rbx
mulx r13, rbx, [ rsi + 0x30 ]
mov rax, rbx
adcx rax, [ rsp + 0x30 ]
mov [ rsp + 0xf8 ], rdi
mov rdi, r13
adcx rdi, [ rsp + 0x28 ]
test al, al
adox rax, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x58 ]
mov [ rsp + 0x100 ], r14
mov [ rsp + 0x108 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
adcx rax, r14
mov [ rsp + 0x110 ], r15
mov r15, rcx
adcx r15, rdi
mov rdi, rbx
mov [ rsp + 0x118 ], r15
xor r15, r15
adox rdi, rbx
adox r13, r13
adcx rdi, [ rsp + 0x30 ]
adcx r13, [ rsp + 0x28 ]
test al, al
adox rdi, [ rsp + 0x70 ]
adox r13, [ rsp + 0x58 ]
mov rbx, r12
shrd rbx, r10, 56
mulx r15, r10, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rbx
mov rbx, 0xffffffffffffff 
and r12, rbx
adox rax, r9
adox r11, [ rsp + 0x118 ]
adcx rdi, r14
adcx rcx, r13
mov r9, r10
xor r14, r14
adox r9, [ rsp + 0x20 ]
mov r13, r15
adox r13, [ rsp + 0x18 ]
mov rbx, r9
adcx rbx, [ rsp + 0x90 ]
mov [ rsp + 0x128 ], r12
mov r12, r13
adcx r12, [ rsp + 0x78 ]
mov [ rsp + 0x130 ], r11
xor r11, r11
adox r9, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
adcx r9, r10
adcx r15, r13
xor r14, r14
adox r9, [ rsp + 0x90 ]
adox r15, [ rsp + 0x78 ]
adcx rdi, [ rsp - 0x10 ]
adcx rcx, [ rsp - 0x18 ]
mulx r10, r11, [ rsi + 0x18 ]
add rbx, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x8 ]
test al, al
adox r9, [ rsp + 0x0 ]
adox r15, [ rsp - 0x8 ]
adcx r9, [ rsp + 0x40 ]
adcx r15, [ rsp + 0x38 ]
mov r13, r11
test al, al
adox r13, [ rsp + 0xd0 ]
mov [ rsp + 0x138 ], rax
mov rax, r10
adox rax, [ rsp + 0xc8 ]
adcx r8, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
add r8, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0xa8 ]
add r13, [ rsp - 0x20 ]
adcx rax, [ rsp - 0x28 ]
mov r14, rdx
mov rdx, [ rsp + 0xd8 ]
mov [ rsp + 0x140 ], r12
mov [ rsp + 0x148 ], rbx
mulx rbx, r12, [ rsi + 0x0 ]
test al, al
adox r13, r12
adox rbx, rax
mov rdx, [ rsi + 0x10 ]
mulx r12, rax, rdx
mov rdx, r14
mov [ rsp + 0x150 ], rbx
mulx rbx, r14, [ rsi + 0x0 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], rcx
mulx rcx, r13, [ rsi + 0x8 ]
adcx r8, [ rsp + 0x68 ]
adcx rbp, [ rsp + 0x60 ]
test al, al
adox r8, r14
adox rbx, rbp
adcx r9, rax
adcx r12, r15
xor rdx, rdx
adox r9, r13
mov r15, rcx
adox r15, r12
mov rax, 0x38 
bzhi r14, r8, rax
shrd r8, rbx, 56
test al, al
adox rdi, [ rsp - 0x30 ]
mov rbp, [ rsp - 0x38 ]
adox rbp, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x48 ]
add r9, [ rsp + 0x88 ]
adcx r15, [ rsp + 0x80 ]
xor rbx, rbx
adox r9, [ rsp + 0x120 ]
adox r15, rbx
mov rdx, r8
adcx rdx, r9
adc r15, 0x0
mov r12, r11
xor r9, r9
adox r12, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe8 ]
mov rbx, [ rsp + 0x148 ]
adcx rbx, [ rsp + 0x40 ]
mov r11, [ rsp + 0x140 ]
adcx r11, [ rsp + 0x38 ]
add rbx, r13
adcx rcx, r11
add rbx, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r11, rdx
bzhi rdx, r13, rax
adox r12, r11
adox r9, r10
xor r10, r10
adox rdi, [ rsp + 0xa0 ]
adox rbp, [ rsp + 0x98 ]
shrd r13, r15, 56
add rdi, r13
adc rbp, 0x0
xor r15, r15
adox r8, rbx
adox rcx, r15
mov r10, rdi
shrd r10, rbp, 56
bzhi rbx, r8, rax
shrd r8, rcx, 56
mov r11, r8
add r11, [ rsp + 0x138 ]
mov r13, [ rsp + 0x130 ]
adc r13, 0x0
mov rbp, r11
shrd rbp, r13, 56
mov rcx, rbp
add rcx, [ rsp + 0x158 ]
mov r8, [ rsp + 0x150 ]
adc r8, 0x0
xor r13, r13
adox r12, [ rsp + 0x110 ]
adox r9, [ rsp + 0x108 ]
bzhi r15, rcx, rax
shrd rcx, r8, 56
xor rbp, rbp
adox r12, [ rsp + 0xb8 ]
adox r9, [ rsp + 0xb0 ]
adcx r12, [ rsp + 0x100 ]
adcx r9, [ rsp + 0xf8 ]
add rcx, [ rsp + 0x128 ]
mov r13, rcx
shr r13, 56
add r12, r10
adc r9, 0x0
mov r10, r12
shrd r10, r9, 56
bzhi r8, rcx, rax
bzhi rcx, r12, rax
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x30 ], rcx
lea r10, [ r10 + r14 ]
bzhi r14, r10, rax
mov [ r12 + 0x38 ], r14
shr r10, 56
lea rbx, [ rbx + r10 ]
lea rdx, [ rdx + r10 ]
lea r13, [ r13 + rdx ]
bzhi r9, r13, rax
bzhi rcx, rbx, rax
mov [ r12 + 0x20 ], r9
mov [ r12 + 0x0 ], rcx
shr r13, 56
bzhi r14, rdi, rax
bzhi rdi, r11, rax
shr rbx, 56
lea rbx, [ rbx + rdi ]
mov [ r12 + 0x18 ], r8
lea r13, [ r13 + r14 ]
mov [ r12 + 0x10 ], r15
mov [ r12 + 0x28 ], r13
mov [ r12 + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 488
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0285
; seed 2532890515148842 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 31298 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=204, initial num_batches=31): 1112 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.035529426800434534
; number reverted permutation / tried permutation: 390 / 520 =75.000%
; number reverted decision / tried decision: 333 / 479 =69.520%
; validated in 3.261s
