SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 528
mov rax, 0x2 
shlx r10, [ rsi + 0x30 ], rax
mov r11, 0x1 
shlx rdx, [ rsi + 0x8 ], r11
mov rcx, [ rsi + 0x38 ]
lea r8, [rcx + rcx]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
shl rbx, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
lea r13, [rdx + rdx]
mov rdx, r10
mov [ rsp - 0x60 ], r14
mulx r14, r10, [ rsi + 0x28 ]
xchg rdx, r13
mov [ rsp - 0x58 ], r15
mulx rax, r15, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov rdi, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], rax
mov rax, rdi
shl rax, 0x1
xchg rdx, rbx
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r12
mulx r12, rdi, rax
xor rdx, rdx
adox r9, rdi
adox r12, r11
mov r11, 0x2 
shlx rdi, [ rsi + 0x38 ], r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r12
mulx r12, r11, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], rbp
mulx rbp, r9, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rcx
mulx rcx, r8, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r8
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, r8
mov [ rsp + 0x20 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rcx
xor rcx, rcx
adox r10, r11
adox r12, r14
mov r14, 0x2 
shlx r11, [ rsi + 0x28 ], r14
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r8
mulx r8, r14, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r14
mulx r14, r8, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r10
mulx r10, r12, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r10
mov [ rsp + 0x60 ], r12
mulx r12, r10, r13
imul rdx, [ rsi + 0x20 ], 0x2
mov [ rsp + 0x68 ], r12
mulx r12, r13, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r10
mulx r10, r12, rcx
mov rdx, r11
mulx rcx, r11, [ rsi + 0x20 ]
xor rdx, rdx
adox r11, r8
adox r14, rcx
mov rdx, r13
mulx r8, r13, [ rsi + 0x18 ]
xchg rdx, rax
mov [ rsp + 0x98 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r10
mov [ rsp + 0xb0 ], r12
mulx r12, r10, r15
adcx r11, r9
adcx rbp, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, r9, rdx
add rcx, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r9
mulx r9, r14, [ rsp + 0x0 ]
mov rdx, 0x2 
mov [ rsp + 0xc8 ], r9
shlx r9, [ rsi + 0x40 ], rdx
mov rdx, r9
mov [ rsp + 0xd0 ], r14
mulx r14, r9, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r11
mov [ rsp + 0xe8 ], r12
mulx r12, r11, r15
xor rdx, rdx
adox rcx, [ rsp + 0x10 ]
adox r8, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], r11
mulx r11, r12, [ rsp - 0x8 ]
mov rdx, r9
adcx rdx, [ rsp + 0x50 ]
adcx r14, [ rsp + 0x48 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x100 ], r11
mov [ rsp + 0x108 ], r12
mulx r12, r11, rdi
mov rdx, r15
mulx rdi, r15, [ rsi + 0x30 ]
xor rdx, rdx
adox r9, [ rsp + 0x20 ]
adox r14, [ rsp + 0x18 ]
adcx r9, [ rsp + 0x30 ]
adcx r14, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x110 ], r14
mov [ rsp + 0x118 ], r9
mulx r9, r14, [ rsp - 0x8 ]
xor rdx, rdx
adox r15, r11
adox r12, rdi
mov rdx, [ rsi + 0x28 ]
mulx rdi, r11, rbp
mov rdx, rbp
mov [ rsp + 0x120 ], r8
mulx r8, rbp, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], rcx
mov [ rsp + 0x130 ], r10
mulx r10, rcx, [ rsi + 0x20 ]
adcx r15, rcx
adcx r10, r12
add r14, rbp
adcx r8, r9
mulx r12, r9, [ rsi + 0x10 ]
mov rbp, r11
test al, al
adox rbp, [ rsp + 0x40 ]
adox rdi, [ rsp + 0x38 ]
adcx rbp, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x28 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r8
mulx r8, rcx, [ rsp - 0x8 ]
mov rdx, 0x1 
mov [ rsp + 0x140 ], r14
shlx r14, [ rsi + 0x40 ], rdx
xor rdx, rdx
adox r15, [ rsp + 0xb0 ]
adox r10, [ rsp + 0xa8 ]
mov rdx, r14
mov [ rsp + 0x148 ], r12
mulx r12, r14, [ rsi + 0x40 ]
adcx r15, [ rsp + 0x60 ]
adcx r10, [ rsp + 0x58 ]
mov [ rsp + 0x150 ], r10
mov r10, [ rsp + 0x130 ]
mov [ rsp + 0x158 ], r15
mov r15, r10
test al, al
adox r15, [ rsp - 0x18 ]
mov [ rsp + 0x160 ], r9
mov r9, [ rsp + 0xe8 ]
adox r9, [ rsp - 0x20 ]
adcx r15, rcx
adcx r8, r9
add r14, [ rsp + 0xa0 ]
adcx r12, [ rsp + 0x98 ]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, r13
add r14, rcx
adcx r9, r12
test al, al
adox r14, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r12, rbx
mov rdx, r10
mulx rbx, r10, [ rsi + 0x0 ]
adcx r15, r10
adcx rbx, r8
test al, al
adox rbp, r12
adox rcx, rdi
mov rdx, [ rsi + 0x8 ]
mulx r8, rdi, r11
mov rdx, [ rsi + 0x18 ]
mulx r10, r12, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x168 ], rbx
mov [ rsp + 0x170 ], r15
mulx r15, rbx, r11
adcx rbp, [ rsp + 0x88 ]
adcx rcx, [ rsp + 0x80 ]
mov rdx, rdi
add rdx, [ rsp + 0xe0 ]
adcx r8, [ rsp + 0xd8 ]
xor r11, r11
adox rbx, r12
adox r10, r15
adcx rbx, [ rsp + 0x78 ]
adcx r10, [ rsp + 0x70 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r12, r13
test al, al
adox rdi, [ rsp + 0xc0 ]
adox r8, [ rsp + 0xb8 ]
mov rdx, [ rsp + 0x128 ]
adcx rdx, [ rsp + 0x160 ]
mov [ rsp + 0x178 ], r9
mov r9, [ rsp + 0x120 ]
adcx r9, [ rsp + 0x148 ]
add rdx, [ rsp + 0xd0 ]
adcx r9, [ rsp + 0xc8 ]
test al, al
adox rbx, r12
adox r15, r10
mov r10, rdi
shrd r10, r8, 58
shr r8, 58
xor r12, r12
adox rdx, r10
adox r8, r9
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, rax
adcx rbx, [ rsp + 0xf8 ]
adcx r15, [ rsp + 0xf0 ]
mov rdx, [ rsp - 0x40 ]
mov rax, rdx
mov [ rsp + 0x180 ], r15
xor r15, r15
adox rax, [ rsp + 0x140 ]
mov r12, [ rsp - 0x48 ]
adox r12, [ rsp + 0x138 ]
mov rdx, r11
shrd rdx, r8, 58
shr r8, 58
xchg rdx, r13
mov [ rsp + 0x188 ], rbx
mulx rbx, r15, [ rsi + 0x0 ]
test al, al
adox rax, r9
adox r10, r12
mov rdx, r13
adcx rdx, [ rsp + 0x118 ]
adcx r8, [ rsp + 0x110 ]
xor r9, r9
adox rax, r15
adox rbx, r10
mov r12, rdx
shrd r12, r8, 58
shr r8, 58
mov r13, r12
test al, al
adox r13, [ rsp + 0x158 ]
adox r8, [ rsp + 0x150 ]
mov r15, r13
shrd r15, r8, 58
shr r8, 58
xor r10, r10
adox rbp, r15
adox r8, rcx
mov r9, 0x3ffffffffffffff 
and r13, r9
mov rcx, rbp
shrd rcx, r8, 58
shr r8, 58
and rbp, r9
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x20 ], rbp
adox rax, rcx
adox r8, rbx
mov rbx, rax
shrd rbx, r8, 58
shr r8, 58
xor r15, r15
adox r14, [ rsp + 0x108 ]
mov r10, [ rsp + 0x178 ]
adox r10, [ rsp + 0x100 ]
mov rcx, rbx
adcx rcx, [ rsp + 0x188 ]
adcx r8, [ rsp + 0x180 ]
mov rbp, rcx
shrd rbp, r8, 58
shr r8, 58
xor rbx, rbx
adox r14, rbp
adox r8, r10
mov r15, r14
shrd r15, r8, 58
shr r8, 58
mov r10, r15
xor rbp, rbp
adox r10, [ rsp + 0x170 ]
adox r8, [ rsp + 0x168 ]
and r14, r9
mov rbx, r10
shrd rbx, r8, 57
shr r8, 57
and rcx, r9
mov [ r12 + 0x38 ], r14
mov [ r12 + 0x30 ], rcx
and rdi, r9
and rax, r9
adox rbx, rdi
adox r8, rbp
mov r15, rbx
shrd r15, r8, 58
mov [ r12 + 0x28 ], rax
and rbx, r9
mov r14, 0x1ffffffffffffff 
and r10, r14
and r11, r9
mov [ r12 + 0x40 ], r10
mov [ r12 + 0x0 ], rbx
and rdx, r9
lea r15, [ r15 + r11 ]
mov rcx, r15
and rcx, r9
mov [ r12 + 0x8 ], rcx
shr r15, 58
lea r15, [ r15 + rdx ]
mov [ r12 + 0x18 ], r13
mov [ r12 + 0x10 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 528
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1928
; seed 3377402219936939 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 20852 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 605 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.029014003452906195
; number reverted permutation / tried permutation: 317 / 485 =65.361%
; number reverted decision / tried decision: 299 / 514 =58.171%
; validated in 2.065s
