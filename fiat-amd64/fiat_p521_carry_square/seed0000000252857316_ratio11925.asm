SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 496
imul rax, [ rsi + 0x28 ], 0x2
mov r10, [ rsi + 0x20 ]
mov r11, r10
shl r11, 0x1
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, rdx
mov rdx, [ rsi + 0x38 ]
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x30 ]
mov r9, rdx
shl r9, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [ 4 * rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbx
mov rdx, [ rsi + 0x40 ]
lea rbx, [rdx + rdx]
mov rdx, rax
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov rdi, 0x1 
mov [ rsp - 0x40 ], rax
shlx rax, [ rsi + 0x8 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], rcx
mulx rcx, rbx, rbp
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x28 ], r10
mov r10, rdx
shl r10, 0x2
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], rcx
mov rcx, rdx
shl rcx, 0x2
mov rdx, rcx
mov [ rsp - 0x18 ], rbx
mulx rbx, rcx, [ rsi + 0x28 ]
xchg rdx, rdi
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r12
mulx r12, r13, [ rsi + 0x10 ]
xchg rdx, rdi
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r11
mov r11, [ rsi + 0x38 ]
mov [ rsp + 0x18 ], rax
mov rax, r11
shl rax, 0x2
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], rcx
mulx rcx, rbx, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], rbx
mulx rbx, rcx, rax
mov rdx, rax
mov [ rsp + 0x40 ], rbx
mulx rbx, rax, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], rax
mov [ rsp + 0x58 ], rcx
mulx rcx, rax, r9
mov rdx, r11
mov [ rsp + 0x60 ], rcx
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, r10
mov [ rsp + 0x68 ], rax
mulx rax, r10, [ rsi + 0x38 ]
test al, al
adox r14, r11
adox rcx, r15
mulx r11, r15, [ rsi + 0x30 ]
xchg rdx, rbx
mov [ rsp + 0x70 ], r11
mov [ rsp + 0x78 ], r15
mulx r15, r11, [ rsi + 0x10 ]
adcx r14, r11
adcx r15, rcx
xchg rdx, r8
mulx r11, rcx, [ rsi + 0x38 ]
xchg rdx, rdi
mov [ rsp + 0x80 ], r11
mov [ rsp + 0x88 ], rcx
mulx rcx, r11, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], rax
xor rax, rax
adox r11, r12
adox r13, rcx
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx rax, rcx, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], rcx
mulx rcx, rax, rbx
adcx r11, [ rsp + 0x58 ]
adcx r13, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa8 ], r10
mov r10, rdx
shl r10, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], rcx
mov [ rsp + 0xb8 ], rax
mulx rax, rcx, r8
mov rdx, rcx
test al, al
adox rdx, [ rsp + 0x28 ]
adox rax, [ rsp + 0x20 ]
xchg rdx, r10
mov [ rsp + 0xc0 ], r13
mulx r13, rcx, [ rsi + 0x8 ]
xchg rdx, rbx
mov [ rsp + 0xc8 ], r13
mov [ rsp + 0xd0 ], rcx
mulx rcx, r13, [ rsi + 0x8 ]
adcx r14, r13
adcx rcx, r15
mulx r13, r15, [ rsi + 0x18 ]
test al, al
adox r10, r15
adox r13, rax
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r13
mulx r13, r15, rdx
adcx r14, r15
adcx r13, rcx
mov rdx, r14
shrd rdx, r13, 58
shr r13, 58
mov rcx, 0x3a 
bzhi r15, r14, rcx
adox r11, [ rsp + 0x38 ]
mov r14, [ rsp + 0x30 ]
adox r14, [ rsp + 0xc0 ]
mov rcx, rdx
mov rdx, [ rsp + 0x18 ]
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], r10
mulx r10, r15, [ rsi + 0x0 ]
add r11, r15
adcx r10, r14
test al, al
adox r11, rcx
adox r13, r10
mov rdx, [ rsi + 0x28 ]
mulx r14, rcx, r8
mov rdx, r9
mulx r8, r9, [ rsi + 0x30 ]
adcx r9, rcx
adcx r14, r8
xchg rdx, rax
mulx r10, r15, [ rsi + 0x20 ]
mov rdx, rbp
mulx rcx, rbp, [ rsi + 0x8 ]
mov rdx, rbx
mulx r8, rbx, [ rsi + 0x0 ]
test al, al
adox r9, r15
adox r10, r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r13
mulx r13, r15, [ rsp + 0x10 ]
adcx r9, rbp
adcx rcx, r10
xor rdx, rdx
adox r9, rbx
adox r8, rcx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rbp, [ rsp + 0x10 ]
mov rdx, [ rsp - 0x8 ]
mov r10, rdx
adcx r10, [ rsp + 0xe8 ]
mov rcx, [ rsp - 0x10 ]
adcx rcx, [ rsp + 0xd8 ]
xor rdx, rdx
adox r10, [ rsp - 0x18 ]
adox rcx, [ rsp - 0x20 ]
mov rdx, [ rsp + 0xf0 ]
mov [ rsp + 0xf8 ], r13
mov r13, r11
shrd r13, rdx, 58
shr rdx, 58
test al, al
adox r10, r13
adox rdx, rcx
mov rcx, r10
shrd rcx, rdx, 58
shr rdx, 58
test al, al
adox r9, rcx
adox rdx, r8
mov r8, [ rsp + 0x50 ]
adcx r8, [ rsp + 0xb8 ]
mov r13, [ rsp + 0x48 ]
adcx r13, [ rsp + 0xb0 ]
mov rcx, 0x3ffffffffffffff 
and r10, rcx
adox r8, [ rsp - 0x28 ]
adox r13, [ rsp - 0x30 ]
adcx r8, [ rsp + 0xd0 ]
adcx r13, [ rsp + 0xc8 ]
mov rcx, rdx
mov rdx, [ rsp + 0x10 ]
mov [ rsp + 0x100 ], r10
mov [ rsp + 0x108 ], r15
mulx r15, r10, [ rsi + 0x0 ]
add r8, r10
adcx r15, r13
mov r13, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x110 ], rbx
mulx rbx, r10, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], rbx
mulx rbx, rbp, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], rbx
mov [ rsp + 0x130 ], rbp
mulx rbp, rbx, rdx
mov rdx, r9
shrd rdx, rcx, 58
shr rcx, 58
test al, al
adox r8, rdx
adox rcx, r15
mov r15, r8
shrd r15, rcx, 58
shr rcx, 58
mov rdx, 0x3ffffffffffffff 
and r9, rdx
mov rdx, r13
mov [ rsp + 0x138 ], r9
mulx r9, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], rcx
mov [ rsp + 0x148 ], r15
mulx r15, rcx, rax
adox r10, r13
adox r9, [ rsp + 0x120 ]
mov rdx, 0x3ffffffffffffff 
and r8, rdx
adox r10, [ rsp + 0x8 ]
adox r9, [ rsp + 0x0 ]
mov rax, rbx
adcx rax, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, rbx, rdx
xor rdx, rdx
adox rbx, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
adcx rbx, [ rsp + 0x68 ]
adcx r13, [ rsp + 0x60 ]
mov [ rsp + 0x150 ], r8
mov r8, [ rsp + 0x78 ]
mov [ rsp + 0x158 ], r15
mov r15, r8
test al, al
adox r15, [ rsp + 0x88 ]
mov [ rsp + 0x160 ], rcx
mov rcx, [ rsp + 0x70 ]
adox rcx, [ rsp + 0x80 ]
mov rdx, r14
mulx r8, r14, [ rsi + 0x10 ]
adcx r15, r14
adcx r8, rcx
test al, al
adox r10, [ rsp + 0xa0 ]
adox r9, [ rsp + 0x98 ]
mov rdx, rdi
mulx rcx, rdi, [ rsi + 0x8 ]
adcx r15, [ rsp + 0x118 ]
adcx r8, [ rsp + 0x110 ]
test al, al
adox rbx, rdi
adox rcx, r13
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r14, r12
mov rdx, r12
mov [ rsp + 0x168 ], rcx
mulx rcx, r12, [ rsi + 0x8 ]
adcx r15, r14
adcx rdi, r8
xor rdx, rdx
adox r15, [ rsp + 0x148 ]
adox rdi, [ rsp + 0x140 ]
adcx rax, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0xf8 ]
mov r8, r15
shrd r8, rdi, 58
shr rdi, 58
test al, al
adox rax, r12
adox rcx, rbp
adcx rax, [ rsp + 0x160 ]
adcx rcx, [ rsp + 0x158 ]
add rax, r8
adcx rdi, rcx
mov r14, rax
shrd r14, rdi, 58
shr rdi, 58
mov rdx, r13
mulx r12, r13, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, r13
adox r12, r9
adcx r10, r14
adcx rdi, r12
mov r9, 0x3ffffffffffffff 
mov rbp, r10
and rbp, r9
shrd r10, rdi, 58
shr rdi, 58
test al, al
adox rbx, [ rsp + 0x130 ]
mov r8, [ rsp + 0x128 ]
adox r8, [ rsp + 0x168 ]
adcx rbx, r10
adcx rdi, r8
mov rcx, rbx
shrd rcx, rdi, 57
shr rdi, 57
xor r14, r14
adox rcx, [ rsp + 0xe0 ]
adox rdi, r14
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], rbp
mov r13, rcx
and r13, r9
and r11, r9
mov [ rdx + 0x0 ], r13
shrd rcx, rdi, 58
lea rcx, [ rcx + r11 ]
mov r12, rcx
and r12, r9
shr rcx, 58
add rcx, [ rsp + 0x100 ]
mov rbp, [ rsp + 0x150 ]
mov [ rdx + 0x20 ], rbp
mov [ rdx + 0x8 ], r12
and rax, r9
mov rbp, 0x1ffffffffffffff 
and rbx, rbp
mov r10, [ rsp + 0x138 ]
mov [ rdx + 0x18 ], r10
and r15, r9
mov [ rdx + 0x28 ], r15
mov [ rdx + 0x30 ], rax
mov [ rdx + 0x40 ], rbx
mov [ rdx + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 496
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1925
; seed 2298704771753040 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2564227 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=97, initial num_batches=31): 86500 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.033733362919897494
; number reverted permutation / tried permutation: 63320 / 89960 =70.387%
; number reverted decision / tried decision: 55432 / 90039 =61.564%
; validated in 1.55s
