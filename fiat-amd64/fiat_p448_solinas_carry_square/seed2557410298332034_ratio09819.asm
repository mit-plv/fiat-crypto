SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 544
mov rax, [ rsi + 0x8 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x28 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x28 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x0 ]
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
imul rdx, [ rsi + 0x18 ], 0x2
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov rdx, r12
mulx r10, r12, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, rdx
mov rdx, rdi
test al, al
adox rdx, rax
mov [ rsp - 0x40 ], rcx
mov rcx, r11
adox rcx, r8
mov [ rsp - 0x38 ], r10
mov r10, [ rsi + 0x38 ]
mov [ rsp - 0x30 ], r12
mov r12, r10
shl r12, 0x1
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, rdx
mov rdx, r12
mov [ rsp - 0x18 ], r13
mulx r13, r12, [ rsi + 0x10 ]
xchg rdx, r15
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r13
mov r13, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r14
mov r14, r13
shl r14, 0x1
xchg rdx, r15
mov [ rsp + 0x10 ], r12
mulx r12, r13, [ rsi + 0x0 ]
xchg rdx, r14
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r13
mov r13, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r12
lea r12, [r13 + r13]
xchg rdx, r12
mov [ rsp + 0x38 ], rbp
mulx rbp, r13, [ rsi + 0x20 ]
xchg rdx, r14
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rcx
mulx rcx, rbx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r9
mulx r9, rbx, r12
mov rdx, r15
mulx r12, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r12
mov [ rsp + 0x70 ], r15
mulx r15, r12, r14
test al, al
adox r10, r13
mov rdx, rbp
adox rdx, [ rsp + 0x48 ]
mov [ rsp + 0x78 ], r9
mov r9, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], rbx
lea rbx, [r9 + r9]
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], r15
mulx r15, r10, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r9
mov [ rsp + 0xa0 ], r12
mulx r12, r9, [ rsp + 0x60 ]
mov rdx, rbx
mov [ rsp + 0xa8 ], r12
mulx r12, rbx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r12
mov [ rsp + 0xb8 ], rbx
mulx rbx, r12, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], rbx
mov rbx, rdi
adcx rbx, rdi
adcx r8, r8
xor rdi, rdi
adox rbx, rax
adox r11, r8
mulx r8, rax, [ rsi + 0x10 ]
adcx rbx, r13
adcx rbp, r11
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx rdi, r11, rcx
mov rdx, r10
add rdx, r10
mov [ rsp + 0xc8 ], r8
mov r8, r15
adcx r8, r15
add rdx, r9
adcx r8, [ rsp + 0xa8 ]
mov [ rsp + 0xd0 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], r12
mov [ rsp + 0xe0 ], rbp
mulx rbp, r12, [ rsp + 0x60 ]
mov rdx, r11
test al, al
adox rdx, [ rsp + 0x40 ]
mov [ rsp + 0xe8 ], rbp
mov rbp, rdi
adox rbp, [ rsp + 0x38 ]
adcx rax, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x90 ]
add r10, r9
adcx r15, [ rsp + 0xa8 ]
xor r9, r9
adox r10, [ rsp + 0xa0 ]
adox r15, [ rsp + 0x90 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], rbp
mulx rbp, r12, r13
mov rdx, rcx
mulx r13, rcx, [ rsi + 0x20 ]
adcx r10, [ rsp + 0x10 ]
adcx r15, [ rsp - 0x8 ]
xchg rdx, r14
mov [ rsp + 0x100 ], rbp
mov [ rsp + 0x108 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
test al, al
adox rbp, rcx
adox r13, r12
mov rcx, rbp
adcx rcx, [ rsp + 0x30 ]
mov r12, r13
adcx r12, [ rsp + 0x28 ]
mov [ rsp + 0x110 ], r12
xor r12, r12
adox r10, [ rsp - 0x20 ]
adox r15, [ rsp - 0x28 ]
xchg rdx, r14
mov [ rsp + 0x118 ], r15
mulx r15, r12, [ rsi + 0x18 ]
adcx rax, [ rsp + 0x10 ]
adcx r8, [ rsp - 0x8 ]
xor rdx, rdx
adox rbx, r12
mov [ rsp + 0x120 ], r10
mov r10, r15
adox r10, [ rsp + 0xe0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x128 ], r10
mov [ rsp + 0x130 ], rbx
mulx rbx, r10, rdx
mov rdx, r9
adcx rdx, [ rsp + 0x40 ]
mov [ rsp + 0x138 ], r8
mov r8, [ rsp + 0x38 ]
adcx r8, [ rsp + 0xf8 ]
mov [ rsp + 0x140 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], rbx
mov [ rsp + 0x150 ], r10
mulx r10, rbx, rdx
mov rdx, r12
mov [ rsp + 0x158 ], r10
xor r10, r10
adox rdx, [ rsp + 0x88 ]
adox r15, [ rsp + 0x98 ]
adcx rcx, [ rsp + 0x8 ]
mov r12, [ rsp + 0x110 ]
adcx r12, [ rsp + 0x0 ]
mov [ rsp + 0x160 ], rbx
xor rbx, rbx
adox rax, r11
adox rdi, r8
mov r10, rcx
shrd r10, r12, 56
add rax, [ rsp + 0x150 ]
adcx rdi, [ rsp + 0x148 ]
add rax, [ rsp + 0xf0 ]
adcx rdi, [ rsp + 0xe8 ]
xor r11, r11
adox rdx, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
adcx rbp, [ rsp + 0xd8 ]
adcx r13, [ rsp + 0xc0 ]
mov rbx, [ rsp + 0x140 ]
xor r8, r8
adox rbx, [ rsp - 0x30 ]
mov r11, [ rsp + 0x138 ]
adox r11, [ rsp - 0x38 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x168 ], r10
mulx r10, r8, [ rsp + 0x60 ]
adcx rbx, [ rsp + 0xb8 ]
adcx r11, [ rsp + 0xb0 ]
xor rdx, rdx
adox rbp, r8
adox r10, r13
mov rdx, [ rsi + 0x8 ]
mulx r8, r13, r14
mov rdx, r14
mov [ rsp + 0x170 ], r15
mulx r15, r14, [ rsi + 0x10 ]
adcx rbp, r13
adcx r8, r10
add r9, [ rsp + 0x150 ]
mov r10, [ rsp + 0xf8 ]
adcx r10, [ rsp + 0x148 ]
test al, al
adox r9, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe8 ]
adcx r9, r14
mov r13, r15
adcx r13, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x178 ], r12
mov [ rsp + 0x180 ], rdi
mulx rdi, r12, rdx
xor rdx, rdx
adox r9, [ rsp + 0x58 ]
adox r13, [ rsp + 0x50 ]
mov [ rsp + 0x188 ], rax
mov rax, r12
adcx rax, [ rsp + 0x130 ]
adcx rdi, [ rsp + 0x128 ]
add rax, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0xc8 ]
test al, al
adox rbx, [ rsp - 0x40 ]
adox r11, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r11
mulx r11, r12, rdx
mov rdx, r10
mov [ rsp + 0x198 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
adcx r9, r12
adcx r11, r13
add rbp, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x18 ]
mov rdx, r14
add rdx, [ rsp + 0x188 ]
adcx r15, [ rsp + 0x180 ]
xor r14, r14
adox rdx, [ rsp + 0x160 ]
adox r15, [ rsp + 0x158 ]
adcx rdx, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x50 ]
mov r13, rdx
mov rdx, [ rsp + 0x60 ]
mulx r14, r12, [ rsi + 0x8 ]
test al, al
adox rax, r12
adox r14, rdi
mov rdx, rbp
shrd rdx, r8, 56
mov rdi, rdx
xor r8, r8
adox rdi, r9
adox r11, r8
adcx rax, r10
adcx rbx, r14
mov r10, rdi
shrd r10, r11, 56
mov r9, r10
add r9, [ rsp + 0x120 ]
mov r12, [ rsp + 0x118 ]
adc r12, 0x0
mov r14, 0xffffffffffffff 
and rdi, r14
mov r11, [ rsp + 0x178 ]
adox r11, [ rsp + 0x80 ]
mov r10, [ rsp + 0x170 ]
adox r10, [ rsp + 0x78 ]
adcx r13, [ rsp + 0x70 ]
adcx r15, [ rsp + 0x68 ]
mov r8, r9
shrd r8, r12, 56
xor r12, r12
adox r13, [ rsp + 0x108 ]
adox r15, [ rsp + 0x100 ]
adcx r13, [ rsp + 0x168 ]
adc r15, 0x0
and rcx, r14
adox rdx, r13
adox r15, r12
mov r13, rdx
shrd r13, r15, 56
and rdx, r14
adox r11, r8
adox r10, r12
mov r8, r11
and r8, r14
shrd r11, r10, 56
lea r11, [ r11 + rcx ]
mov rcx, r11
and rcx, r14
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], rcx
shr r11, 56
mov r10, r13
add r10, [ rsp + 0x198 ]
mov rcx, [ rsp + 0x190 ]
adc rcx, 0x0
mov r13, r10
shrd r13, rcx, 56
and rbp, r14
adox rax, r13
adox rbx, r12
mov rcx, rax
shrd rcx, rbx, 56
lea rcx, [ rcx + rbp ]
mov r13, rcx
shr r13, 56
lea rdi, [ rdi + r13 ]
lea rdx, [ rdx + r13 ]
lea r11, [ r11 + rdx ]
and r9, r14
mov rbp, r11
and rbp, r14
mov rbx, rdi
shr rbx, 56
lea rbx, [ rbx + r9 ]
shr r11, 56
and r10, r14
mov [ r15 + 0x20 ], rbp
lea r11, [ r11 + r10 ]
mov [ r15 + 0x8 ], rbx
mov [ r15 + 0x10 ], r8
and rax, r14
and rcx, r14
mov [ r15 + 0x28 ], r11
mov [ r15 + 0x30 ], rax
mov [ r15 + 0x38 ], rcx
and rdi, r14
mov [ r15 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 544
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9819
; seed 2557410298332034 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 34191 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=79, initial num_batches=31): 968 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.028311543973560293
; number reverted permutation / tried permutation: 277 / 489 =56.646%
; number reverted decision / tried decision: 230 / 510 =45.098%
; validated in 2.442s
