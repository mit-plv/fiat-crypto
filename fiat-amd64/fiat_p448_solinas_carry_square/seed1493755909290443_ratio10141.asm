SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 552
mov rax, 0x1 
shlx r10, [ rsi + 0x10 ], rax
mov r11, [ rsi + 0x38 ]
lea rdx, [r11 + r11]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rax, r9, rdx
mov rdx, r10
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
lea r14, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r14
mov rdx, r11
mov [ rsp - 0x48 ], rax
mulx rax, r11, [ rsi + 0x30 ]
xchg rdx, r14
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r13
mulx r13, r9, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r12
mulx r12, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], rax
mov [ rsp + 0x0 ], r11
mulx r11, rax, r14
mov rdx, r9
add rdx, rax
mov [ rsp + 0x8 ], rcx
mov rcx, r11
adcx rcx, r12
mov [ rsp + 0x10 ], r8
mov r8, rdx
add r8, r9
adcx r12, rcx
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r15
mulx r15, rdi, rdx
mov rdx, r13
mov [ rsp + 0x28 ], r15
mulx r15, r13, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], rdi
mulx rdi, r13, r14
xor rdx, rdx
adox r8, rax
adox r11, r12
imul rax, [ rsi + 0x18 ], 0x2
mov rdx, rax
mulx r12, rax, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], r12
mulx r12, r13, rdx
xor rdx, rdx
adox r8, r13
mov [ rsp + 0x60 ], rax
mov rax, r12
adox rax, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], rax
mulx rax, r11, rdi
adcx r9, r13
adcx r12, rcx
imul rdx, [ rsi + 0x20 ], 0x2
mov rcx, [ rsi + 0x8 ]
mov r13, rcx
shl r13, 0x1
xchg rdx, r15
mov [ rsp + 0x70 ], rax
mulx rax, rcx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r11
mov r11, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], rbp
mov rbp, r11
shl rbp, 0x1
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], r8
mulx r8, r13, rbp
mov rdx, rdi
mov [ rsp + 0x98 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, rbp
mov [ rsp + 0xa0 ], r15
mulx r15, rbp, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], rdi
xor rdi, rdi
adox r9, r13
mov [ rsp + 0xb0 ], r15
mov r15, r8
adox r15, r12
mulx rdi, r12, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
xchg rdx, r14
mov [ rsp + 0xc8 ], r12
mov [ rsp + 0xd0 ], rdi
mulx rdi, r12, [ rsi + 0x20 ]
adcx rcx, r12
adcx rdi, rax
mov rax, rcx
test al, al
adox rax, r10
adox rbx, rdi
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], rbp
mulx rbp, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], r9
mulx r9, r15, [ rsp + 0x98 ]
adcx rcx, r15
adcx r9, rdi
xor rdx, rdx
adox rax, [ rsp + 0x60 ]
adox rbx, [ rsp + 0x58 ]
mov rdx, [ rsp + 0x98 ]
mulx r15, rdi, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r15
mov r15, rax
shrd r15, rbx, 56
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], rdi
mulx rdi, r15, rdx
mov rdx, r15
mov [ rsp + 0x108 ], r9
xor r9, r9
adox rdx, r15
mov [ rsp + 0x110 ], rcx
mov rcx, rdi
adox rcx, rdi
mov [ rsp + 0x118 ], rcx
mov rcx, r13
adcx rcx, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x68 ]
mov r13, rdx
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x120 ], rbp
mulx rbp, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, [ rsp + 0x20 ]
adox r8, [ rsp + 0x18 ]
adcx r13, r12
mov [ rsp + 0x128 ], rbp
mov rbp, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x120 ]
mov rdx, r11
mov [ rsp + 0x130 ], r9
mulx r9, r11, [ rsi + 0x20 ]
add r13, r11
mov [ rsp + 0x138 ], r8
mov r8, r9
adcx r8, rbp
xchg rdx, r10
mov [ rsp + 0x140 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
mov [ rsp + 0x148 ], r8
xor r8, r8
adox r15, r12
adox rdi, [ rsp + 0x120 ]
mulx r8, r12, [ rsi + 0x0 ]
adcx r15, r11
adcx r9, rdi
mov rdx, [ rsp + 0x20 ]
mov r11, rdx
test al, al
adox r11, [ rsp + 0xe8 ]
mov rdi, [ rsp + 0x18 ]
adox rdi, [ rsp + 0xe0 ]
adcx r15, rbp
mov rdx, rcx
adcx rdx, r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], rdi
mulx rdi, r15, r10
xor rdx, rdx
adox r13, rbp
adox rcx, [ rsp + 0x148 ]
mov r10, [ rsp + 0x110 ]
adcx r10, [ rsp + 0xd8 ]
mov rbp, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0xb0 ]
add r10, r15
adcx rdi, rbp
test al, al
adox r10, r12
adox r8, rdi
mov rdx, r14
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, rbx
mulx r15, rbx, [ rsi + 0x10 ]
mov rbp, 0x38 
bzhi rdi, r10, rbp
shrd r10, r8, 56
xor r8, r8
adox r11, [ rsp + 0x10 ]
mov rbp, [ rsp + 0x8 ]
mov [ rsp + 0x160 ], rdi
mov rdi, rbp
adox rdi, [ rsp + 0x158 ]
mov r8, rdx
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0x0 ]
mov [ rsp + 0x178 ], r11
mov r11, r12
adcx r11, [ rsp - 0x8 ]
mov [ rsp + 0x180 ], r11
xor r11, r11
adox r13, [ rsp - 0x10 ]
adox rcx, [ rsp - 0x18 ]
adcx r13, rbx
adcx r15, rcx
mov rbx, [ rsp + 0x150 ]
xor rcx, rcx
adox rbx, [ rsp - 0x20 ]
adox r9, [ rsp - 0x38 ]
mov r11, [ rsp + 0x0 ]
mov [ rsp + 0x188 ], rdx
mov rdx, r11
adcx rdx, r11
mov [ rsp + 0x190 ], r15
mov r15, [ rsp - 0x8 ]
adcx r15, r15
mov r11, [ rsp + 0x140 ]
mov [ rsp + 0x198 ], r13
xor r13, r13
adox r11, [ rsp + 0x40 ]
mov rcx, [ rsp + 0x138 ]
adox rcx, [ rsp + 0x28 ]
adcx rbx, r10
adcx rdi, r9
xor r10, r10
adox rdx, r14
adox r12, r15
mov r13, [ rsp + 0x178 ]
adcx r13, [ rsp - 0x40 ]
mov r14, [ rsp + 0x170 ]
adcx r14, [ rsp - 0x48 ]
test al, al
adox r11, [ rsp + 0x10 ]
adox rbp, rcx
mov r9, r13
adcx r9, [ rsp + 0x168 ]
adc r14, 0x0
mov r15, [ rsp + 0x198 ]
xor rcx, rcx
adox r15, [ rsp + 0xd0 ]
mov r10, [ rsp + 0x190 ]
adox r10, [ rsp + 0xc8 ]
xchg rdx, r8
mulx rcx, r13, [ rsi + 0x0 ]
adcx r15, [ rsp - 0x28 ]
adcx r10, [ rsp - 0x30 ]
mov rdx, r9
shrd rdx, r14, 56
test al, al
adox r11, [ rsp + 0x78 ]
adox rbp, [ rsp + 0x70 ]
adcx r11, r13
adcx rcx, rbp
mov r14, [ rsp + 0x188 ]
xor r13, r13
adox r14, [ rsp + 0x38 ]
mov rbp, [ rsp + 0x180 ]
adox rbp, [ rsp + 0x30 ]
adcx r14, [ rsp + 0x50 ]
adcx rbp, [ rsp + 0x48 ]
mov [ rsp + 0x1a0 ], r10
xor r10, r10
adox r8, [ rsp + 0x38 ]
adox r12, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x50 ]
adcx r12, [ rsp + 0x48 ]
test al, al
adox r8, [ rsp + 0xa8 ]
adox r12, [ rsp + 0xa0 ]
adcx r14, [ rsp + 0x130 ]
adcx rbp, [ rsp + 0x128 ]
xor r13, r13
adox r8, [ rsp + 0x100 ]
adox r12, [ rsp + 0xf0 ]
adcx r14, rdx
adc rbp, 0x0
mov r10, r14
shrd r10, rbp, 56
xor rdx, rdx
adox rbx, r10
adox rdi, rdx
adcx r11, [ rsp + 0xf8 ]
adc rcx, 0x0
xor r13, r13
adox r8, [ rsp + 0xc0 ]
adox r12, [ rsp + 0xb8 ]
mov rdx, r11
adcx rdx, [ rsp + 0x168 ]
adc rcx, 0x0
mov rbp, 0xffffffffffffff 
mov r10, rdx
and r10, rbp
mov r11, rbx
and r11, rbp
shrd rdx, rcx, 56
test al, al
adox r8, rdx
adox r12, r13
mov rcx, r8
shrd rcx, r12, 56
test al, al
adox r15, rcx
mov rdx, [ rsp + 0x1a0 ]
adox rdx, r13
mov r12, r15
and r12, rbp
shrd r15, rdx, 56
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], r11
mov [ rcx + 0x30 ], r12
and rax, rbp
add r15, [ rsp + 0x160 ]
shrd rbx, rdi, 56
lea rbx, [ rbx + rax ]
mov rdi, r15
shr rdi, 56
lea r10, [ r10 + rdi ]
and r8, rbp
and r9, rbp
and r15, rbp
mov r11, rbx
shr r11, 56
lea r11, [ r11 + r10 ]
lea r9, [ r9 + rdi ]
mov rdx, r11
and rdx, rbp
shr r11, 56
lea r11, [ r11 + r8 ]
and r14, rbp
mov [ rcx + 0x28 ], r11
and rbx, rbp
mov r12, r9
and r12, rbp
mov [ rcx + 0x18 ], rbx
shr r9, 56
lea r9, [ r9 + r14 ]
mov [ rcx + 0x8 ], r9
mov [ rcx + 0x38 ], r15
mov [ rcx + 0x0 ], r12
mov [ rcx + 0x20 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 552
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0141
; seed 1493755909290443 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 20426 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=135, initial num_batches=31): 673 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.032948203270341724
; number reverted permutation / tried permutation: 343 / 513 =66.862%
; number reverted decision / tried decision: 264 / 486 =54.321%
; validated in 1.984s
