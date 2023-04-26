SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 512
mov rax, [ rsi + 0x30 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x28 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
imul rdx, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x68 ], r13
mov r13, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
lea r14, [r13 + r13]
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, r14
mov [ rsp - 0x48 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r14
mulx r14, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], rdi
mulx rdi, r14, r13
mov rdx, 0x1 
mov [ rsp - 0x18 ], rdi
shlx rdi, [ rsi + 0x28 ], rdx
mov rdx, r10
mov [ rsp - 0x10 ], r14
mulx r14, r10, [ rsi + 0x8 ]
xchg rdx, rdi
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r10
mulx r10, r14, [ rsi + 0x8 ]
xchg rdx, r15
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], rbx
mulx rbx, r8, rdi
mov rdx, r15
mov [ rsp + 0x30 ], r9
mulx r9, r15, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r9
mov [ rsp + 0x40 ], r15
mulx r15, r9, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r15
imul r15, [ rsi + 0x8 ], 0x2
xchg rdx, rcx
mov [ rsp + 0x50 ], r9
mov [ rsp + 0x58 ], r10
mulx r10, r9, [ rsi + 0x8 ]
mov rdx, rbp
mov [ rsp + 0x60 ], r10
xor r10, r10
adox rdx, rax
mov [ rsp + 0x68 ], r9
mov r9, r11
adox r9, r12
mov r10, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], r14
mov r14, r10
shl r14, 0x1
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r14
mulx r14, r15, r13
test al, al
adox r10, r8
mov rdx, rbx
adox rdx, r9
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r14
mulx r14, r9, rdx
mov rdx, rbp
adcx rdx, rbp
adcx r12, r12
mov rbp, rdx
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], r14
mulx r14, r15, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], r14
mov r14, rdx
mov rdx, [ rsp + 0x78 ]
mov [ rsp + 0xa8 ], r15
mov [ rsp + 0xb0 ], r9
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r9
mov [ rsp + 0xc0 ], r15
mulx r15, r9, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], r9
mulx r9, r15, r14
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xd8 ], r9
lea r9, [rdx + rdx]
add rbp, rax
adcx r11, r12
add rbp, r8
adcx rbx, r11
mov rdx, [ rsi + 0x18 ]
mulx r8, rax, rdx
mov rdx, r9
mulx r12, r9, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r15
mulx r15, r11, [ rsi + 0x10 ]
mov [ rsp + 0xe8 ], r12
mov [ rsp + 0xf0 ], r9
mulx r9, r12, [ rsi + 0x18 ]
add r10, r12
mov [ rsp + 0xf8 ], r15
mov r15, r9
adcx r15, r13
xor r13, r13
adox rbp, r12
adox r9, rbx
mulx r12, rbx, [ rsi + 0x8 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x100 ], r12
mov [ rsp + 0x108 ], rbx
mulx rbx, r12, r14
adcx rbp, rax
adcx r8, r9
test al, al
adox rbp, r12
adox rbx, r8
mov rdx, r13
mulx r14, r13, [ rsi + 0x30 ]
mov rax, r13
adcx rax, r13
mov r9, r14
adcx r9, r14
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], r11
mulx r11, r8, rcx
add rax, r8
mov rdx, r11
adcx rdx, r9
xor r9, r9
adox rbp, [ rsp + 0x70 ]
adox rbx, [ rsp + 0x58 ]
xchg rdx, rdi
mov [ rsp + 0x118 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
adcx r13, r8
adcx r11, r14
xchg rdx, r12
mulx r8, r14, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], r11
mov [ rsp + 0x128 ], r13
mulx r13, r11, [ rsi + 0x20 ]
xor rdx, rdx
adox rbp, r9
adox rdi, rbx
adcx r10, [ rsp + 0xb0 ]
adcx r15, [ rsp + 0x98 ]
xor rbx, rbx
adox rax, [ rsp + 0x30 ]
mov rdx, [ rsp + 0x28 ]
mov r9, rdx
adox r9, [ rsp + 0x118 ]
mov [ rsp + 0x130 ], rdi
mov rdi, r14
adcx rdi, [ rsp + 0x10 ]
mov [ rsp + 0x138 ], rbp
mov rbp, r8
adcx rbp, [ rsp + 0x8 ]
mov [ rsp + 0x140 ], r15
mov r15, rdi
add r15, [ rsp + 0x10 ]
mov [ rsp + 0x148 ], r10
mov r10, rbp
adcx r10, [ rsp + 0x8 ]
test al, al
adox r15, r14
adox r8, r10
adcx rax, [ rsp + 0x110 ]
adcx r9, [ rsp + 0xf8 ]
test al, al
adox rax, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
xchg rdx, r12
mulx r10, r14, [ rsi + 0x28 ]
adcx r14, r11
adcx r13, r10
add rax, [ rsp + 0xa8 ]
adcx r9, [ rsp + 0xa0 ]
mov r11, r14
add r11, [ rsp + 0xd0 ]
mov r10, r13
adcx r10, [ rsp + 0xc8 ]
add rdi, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mov [ rsp + 0x150 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
test al, al
adox rdi, [ rsp + 0x40 ]
adox rbp, [ rsp + 0x38 ]
adcx r14, [ rsp - 0x10 ]
adcx r13, [ rsp - 0x18 ]
mov rdx, [ rsp + 0x128 ]
mov [ rsp + 0x158 ], rax
xor rax, rax
adox rdx, [ rsp + 0x30 ]
adox r12, [ rsp + 0x120 ]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r10
mov [ rsp + 0x168 ], r11
mulx r11, r10, rdx
adcx rax, [ rsp + 0x110 ]
adcx r12, [ rsp + 0xf8 ]
add r15, [ rsp - 0x20 ]
adcx r8, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x170 ], r11
mov [ rsp + 0x178 ], r10
mulx r10, r11, rcx
xor rdx, rdx
adox r15, [ rsp + 0x40 ]
adox r8, [ rsp + 0x38 ]
adcx rax, [ rsp + 0xc0 ]
adcx r12, [ rsp + 0xb8 ]
add rdi, rbx
mov rcx, r9
adcx rcx, rbp
xor rbp, rbp
adox r14, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
adcx r15, rbx
adcx r9, r8
mov rdx, r14
shrd rdx, r13, 56
mov rbx, r11
test al, al
adox rbx, [ rsp + 0x168 ]
adox r10, [ rsp + 0x160 ]
adcx r15, [ rsp + 0x178 ]
adcx r9, [ rsp + 0x170 ]
add rbx, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x8 ]
mov r11, [ rsp + 0x50 ]
mov r8, r11
add r8, [ rsp + 0x158 ]
mov r13, [ rsp + 0x48 ]
adcx r13, [ rsp + 0x150 ]
add rbx, [ rsp + 0xf0 ]
adcx r10, [ rsp + 0xe8 ]
test al, al
adox r15, [ rsp + 0x108 ]
adox r9, [ rsp + 0x100 ]
adcx r15, [ rsp + 0x68 ]
adcx r9, [ rsp + 0x60 ]
mov r11, rbx
shrd r11, r10, 56
test al, al
adox rdi, [ rsp + 0x108 ]
adox rcx, [ rsp + 0x100 ]
adcx r15, [ rsp + 0xe0 ]
adcx r9, [ rsp + 0xd8 ]
xor r10, r10
adox rdi, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov rbp, r11
adcx rbp, rdi
adc rcx, 0x0
mov rdi, 0xffffffffffffff 
and rbx, rdi
adox r15, rdx
adox r9, r10
adcx r11, r15
adc r9, 0x0
mov rdx, [ rsp + 0x148 ]
xor r15, r15
adox rdx, [ rsp + 0x90 ]
mov r10, [ rsp + 0x140 ]
adox r10, [ rsp + 0x88 ]
mov r15, rbp
and r15, rdi
shrd rbp, rcx, 56
xor rcx, rcx
adox rax, rbp
adox r12, rcx
mov rbp, rax
shrd rbp, r12, 56
test al, al
adox rdx, rbp
adox r10, rcx
mov r12, rdx
and r12, rdi
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], r12
mov r12, r11
shrd r12, r9, 56
xor r9, r9
adox r8, r12
adox r13, r9
mov rcx, r8
shrd rcx, r13, 56
mov r12, rcx
test al, al
adox r12, [ rsp + 0x138 ]
mov r13, [ rsp + 0x130 ]
adox r13, r9
mov rcx, r12
and rcx, rdi
shrd r12, r13, 56
lea r12, [ r12 + rbx ]
and r8, rdi
mov rbx, r12
and rbx, rdi
shr r12, 56
and r14, rdi
lea r15, [ r15 + r12 ]
mov r13, r15
and r13, rdi
mov [ rbp + 0x30 ], rcx
shrd rdx, r10, 56
lea rdx, [ rdx + r14 ]
mov r10, rdx
shr r10, 56
and r11, rdi
mov [ rbp + 0x38 ], rbx
and rax, rdi
lea r11, [ r11 + r12 ]
shr r15, 56
lea r15, [ r15 + rax ]
mov [ rbp + 0x8 ], r15
mov [ rbp + 0x0 ], r13
lea r10, [ r10 + r11 ]
mov rcx, r10
and rcx, rdi
shr r10, 56
and rdx, rdi
mov [ rbp + 0x20 ], rcx
lea r10, [ r10 + r8 ]
mov [ rbp + 0x18 ], rdx
mov [ rbp + 0x28 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 512
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0561
; seed 3426016606140756 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 15683 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=117, initial num_batches=31): 512 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.03264681502263597
; number reverted permutation / tried permutation: 337 / 491 =68.635%
; number reverted decision / tried decision: 315 / 508 =62.008%
; validated in 1.415s
