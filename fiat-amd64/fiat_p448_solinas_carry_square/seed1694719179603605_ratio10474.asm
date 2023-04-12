SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 488
mov rdx, [ rsi + 0x38 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x18 ]
mov rdx, r11
shl rdx, 0x1
imul r11, [ rsi + 0x28 ], 0x2
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rdx, 0x1 
mov [ rsp - 0x70 ], r12
shlx r12, [ rsi + 0x20 ], rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x58 ], r15
lea r15, [rdx + rdx]
mov rdx, rax
test al, al
adox rdx, rax
mov [ rsp - 0x50 ], rdi
mov rdi, r10
adox rdi, r10
xchg rdx, r15
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r9
mulx r9, r8, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r8
mulx r8, r9, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], rbp
mulx rbp, r9, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], rbp
mov [ rsp + 0x8 ], r9
mulx r9, rbp, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], rbp
mulx rbp, r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r9
mulx r9, rbp, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r9
mov r9, rdx
shl r9, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], rbx
mulx rbx, rbp, rdx
xor rdx, rdx
adox r15, rbp
mov [ rsp + 0x48 ], r12
mov r12, rbx
adox r12, rdi
mov rdx, r8
mulx rdi, r8, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r14
mulx r14, r15, r9
adcx rax, rbp
adcx rbx, r10
add rax, r15
mov rdx, r14
adcx rdx, rbx
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, r9
mov rdx, r11
mov [ rsp + 0x68 ], r10
mulx r10, r11, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r10
mov r10, r13
mov [ rsp + 0x78 ], r11
xor r11, r11
adox r10, r8
mov [ rsp + 0x80 ], rax
mov rax, rdi
adox rax, [ rsp + 0x60 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], rbx
mov [ rsp + 0x90 ], rbp
mulx rbp, rbx, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], rbx
mulx rbx, rbp, r11
mov rdx, r10
adcx rdx, r13
mov r11, rax
adcx r11, [ rsp + 0x60 ]
imul r13, [ rsi + 0x10 ], 0x2
test al, al
adox rdx, r8
adox rdi, r11
xchg rdx, r13
mulx r11, r8, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], rbx
mov rbx, rdx
mov rdx, [ rsp + 0x48 ]
mov [ rsp + 0xb0 ], rbp
mov [ rsp + 0xb8 ], rdi
mulx rdi, rbp, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], r13
mulx r13, rbp, rdx
mov rdx, rdi
mov [ rsp + 0xd8 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], r11
mov r11, r15
adcx r11, [ rsp + 0x58 ]
adcx r14, [ rsp + 0x50 ]
xchg rdx, rbx
mov [ rsp + 0xe8 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, r12
mov [ rsp + 0xf0 ], rdi
mulx rdi, r12, [ rsi + 0x30 ]
xor rdx, rdx
adox r10, rbp
mov [ rsp + 0xf8 ], r15
mov r15, r13
adox r15, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], r8
mulx r8, rax, rdx
adcx r10, [ rsp + 0x40 ]
adcx r15, [ rsp - 0x8 ]
test al, al
adox r11, [ rsp - 0x30 ]
adox r14, [ rsp - 0x38 ]
adcx r11, rax
adcx r8, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, rax, rbx
mov rdx, rbx
mov [ rsp + 0x108 ], r14
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, r12
test al, al
adox rdx, [ rsp + 0x8 ]
mov [ rsp + 0x110 ], rax
mov rax, rdi
adox rax, [ rsp + 0x0 ]
adcx rdx, [ rsp + 0x90 ]
adcx rax, [ rsp + 0x88 ]
add r11, rbx
adcx r14, r8
xor r8, r8
adox rdx, [ rsp + 0x28 ]
adox rax, [ rsp + 0x20 ]
xchg rdx, r9
mulx r8, rbx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], rax
mov rax, [ rsp - 0x30 ]
mov [ rsp + 0x120 ], r9
mov r9, rax
adcx r9, [ rsp + 0x80 ]
mov [ rsp + 0x128 ], r14
mov r14, [ rsp - 0x38 ]
adcx r14, [ rsp + 0x68 ]
xor rax, rax
adox r10, rbx
mov [ rsp + 0x130 ], r11
mov r11, r8
adox r11, r15
mov r15, r12
adcx r15, r12
adcx rdi, rdi
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r11
mulx r11, rax, rdx
add r9, rax
adcx r11, r14
test al, al
adox r15, [ rsp + 0x8 ]
adox rdi, [ rsp + 0x0 ]
adcx r15, [ rsp + 0x90 ]
adcx rdi, [ rsp + 0x88 ]
test al, al
adox r9, [ rsp + 0x100 ]
adox r11, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x8 ]
lea r14, [rdx + rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], r11
mulx r11, rax, r12
mov rdx, [ rsp + 0x130 ]
adcx rdx, [ rsp + 0x78 ]
mov [ rsp + 0x148 ], r9
mov r9, [ rsp + 0x128 ]
adcx r9, [ rsp + 0x70 ]
mov [ rsp + 0x150 ], r10
mov r10, rbp
test al, al
adox r10, [ rsp + 0xd0 ]
adox r13, [ rsp + 0xb8 ]
adcx rdx, rax
adcx r11, r9
test al, al
adox r10, [ rsp + 0x40 ]
adox r13, [ rsp - 0x8 ]
adcx r10, rbx
adcx r8, r13
xor rbp, rbp
adox r15, [ rsp + 0x28 ]
adox rdi, [ rsp + 0x20 ]
xchg rdx, r14
mulx rax, rbx, [ rsi + 0x0 ]
mov rdx, r12
mulx r9, r12, [ rsi + 0x28 ]
adcx r15, [ rsp + 0x18 ]
adcx rdi, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r13, rdx
test al, al
adox r12, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
adcx r10, r13
adcx rbp, r8
mov rdx, r12
test al, al
adox rdx, [ rsp + 0xe8 ]
mov r8, r9
adox r8, [ rsp + 0xe0 ]
xchg rdx, rcx
mov [ rsp + 0x158 ], r11
mulx r11, r13, [ rsi + 0x0 ]
adcx r10, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
add rcx, [ rsp + 0xb0 ]
adcx r8, [ rsp + 0xa8 ]
add rcx, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
mov [ rsp + 0x160 ], r14
xor r14, r14
adox r12, [ rsp + 0xf8 ]
adox r9, [ rsp + 0xf0 ]
adcx r12, r13
adcx r11, r9
test al, al
adox r15, [ rsp + 0xc8 ]
adox rdi, [ rsp + 0xc0 ]
adcx r15, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
mulx r9, r13, [ rsi + 0x8 ]
mov rdx, r12
shrd rdx, r11, 56
test al, al
adox rcx, [ rsp + 0x38 ]
adox r8, [ rsp + 0x30 ]
adcx r10, r13
adcx r9, rbp
mov rbp, rcx
shrd rbp, r8, 56
mov r11, 0xffffffffffffff 
and rcx, r11
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, rdx
adox r10, [ rsp + 0x110 ]
adox r9, [ rsp + 0x108 ]
adcx r10, r13
adc r9, 0x0
mov rdx, [ rsp + 0x150 ]
add rdx, [ rsp - 0x20 ]
mov r13, [ rsp + 0x138 ]
adcx r13, [ rsp - 0x28 ]
and r12, r11
adox rdx, r8
adox r14, r13
mov r8, rbp
adcx r8, r10
adc r9, 0x0
mov r10, r8
shrd r10, r9, 56
xor r13, r13
adox r15, r10
adox rdi, r13
adcx rbp, rdx
adc r14, 0x0
mov rdx, r15
and rdx, r11
mov r9, rbp
shrd r9, r14, 56
and rbp, r11
shrd r15, rdi, 56
mov r10, rbx
xor rdi, rdi
adox r10, [ rsp + 0x120 ]
adox rax, [ rsp + 0x118 ]
adcx r10, r9
adc rax, 0x0
mov r13, r15
add r13, [ rsp + 0x160 ]
mov rbx, [ rsp + 0x158 ]
adc rbx, 0x0
mov r14, r13
shrd r14, rbx, 56
mov r9, r10
shrd r9, rax, 56
mov r15, r9
test al, al
adox r15, [ rsp + 0x148 ]
mov rax, [ rsp + 0x140 ]
adox rax, rdi
lea r14, [ r14 + rcx ]
mov rcx, r14
shr rcx, 56
lea rbp, [ rbp + rcx ]
mov rbx, rbp
shr rbx, 56
and rbp, r11
and r14, r11
and r10, r11
and r8, r11
lea r8, [ r8 + rcx ]
lea rbx, [ rbx + r10 ]
mov r9, r15
shrd r9, rax, 56
lea r9, [ r9 + r12 ]
and r15, r11
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], r15
mov rax, r9
shr rax, 56
lea rax, [ rax + r8 ]
mov rcx, rax
and rcx, r11
shr rax, 56
lea rax, [ rax + rdx ]
mov [ r12 + 0x28 ], rax
and r9, r11
and r13, r11
mov [ r12 + 0x18 ], r9
mov [ r12 + 0x0 ], rbp
mov [ r12 + 0x20 ], rcx
mov [ r12 + 0x30 ], r13
mov [ r12 + 0x8 ], rbx
mov [ r12 + 0x38 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 488
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0474
; seed 1694719179603605 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 19829 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=124, initial num_batches=31): 627 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.03162035402693025
; number reverted permutation / tried permutation: 327 / 492 =66.463%
; number reverted decision / tried decision: 285 / 507 =56.213%
; validated in 1.821s
