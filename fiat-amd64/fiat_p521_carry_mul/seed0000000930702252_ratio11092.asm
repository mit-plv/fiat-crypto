SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 880
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
lea rcx, [rdx + rdx]
mov rdx, [ rax + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x40 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x60 ], r14
shlx r14, [ rax + 0x10 ], rdx
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x40 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x40 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x38 ], r11
lea r11, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], r9
mulx r9, r10, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r9
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], r8
mulx r8, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x0 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, r11
mov [ rsp + 0x8 ], r9
mulx r9, r11, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r9
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov rdx, r8
mov [ rsp + 0x28 ], r10
mulx r10, r8, [ rsi + 0x38 ]
mov [ rsp + 0x30 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r8
mulx r8, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], r10
mulx r10, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x58 ], r13
mov [ rsp + 0x60 ], rdi
mulx rdi, r13, [ rsi + 0x8 ]
mov rdx, r11
mov [ rsp + 0x68 ], rdi
mulx rdi, r11, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], r13
mov r13, [ rax + 0x18 ]
mov [ rsp + 0x78 ], rdi
lea rdi, [r13 + r13]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r11
mov [ rsp + 0x88 ], r10
mulx r10, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r10
mov [ rsp + 0x98 ], r11
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa0 ], r11
mov [ rsp + 0xa8 ], r10
mulx r10, r11, rdi
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], r8
mulx r8, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], rbp
mulx rbp, r8, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r8
mulx r8, rbp, [ rax + 0x8 ]
xor rdx, rdx
adox r14, r11
adox r10, r15
mov rdx, [ rsi + 0x38 ]
mulx r11, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x40 ]
mov [ rsp + 0xf0 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, rcx
mov [ rsp + 0xf8 ], rbp
mulx rbp, rcx, [ rsi + 0x30 ]
xchg rdx, r8
mov [ rsp + 0x100 ], rbp
mov [ rsp + 0x108 ], rcx
mulx rcx, rbp, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], r10
mulx r10, rbp, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], r10
mov [ rsp + 0x130 ], rbp
mulx rbp, r10, rcx
mov rdx, rcx
mov [ rsp + 0x138 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov [ rsp + 0x140 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r10
mulx r10, rcx, r8
mov rdx, r8
mov [ rsp + 0x158 ], r10
mulx r10, r8, [ rsi + 0x38 ]
xchg rdx, r12
mov [ rsp + 0x160 ], rcx
mov [ rsp + 0x168 ], r10
mulx r10, rcx, [ rsi + 0x40 ]
mov [ rsp + 0x170 ], r10
mov [ rsp + 0x178 ], rcx
mulx rcx, r10, [ rsi + 0x30 ]
test al, al
adox rbx, r15
adox r11, [ rsp + 0xb8 ]
mov r15, [ rax + 0x8 ]
mov [ rsp + 0x180 ], r8
mov r8, r15
shl r8, 0x1
xchg rdx, r8
mov [ rsp + 0x188 ], r14
mulx r14, r15, [ rsi + 0x40 ]
test al, al
adox rbx, [ rsp + 0xb0 ]
adox r11, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r11
mov [ rsp + 0x198 ], rbx
mulx rbx, r11, rdi
adcx r15, [ rsp + 0x60 ]
adcx r14, [ rsp + 0x58 ]
xor rdx, rdx
adox r15, r11
adox rbx, r14
mov rdx, [ rsi + 0x28 ]
mulx r14, r11, r8
adcx r15, r11
adcx r14, rbx
mov rdx, [ rsi + 0x20 ]
mulx r11, rbx, r12
xor rdx, rdx
adox r15, rbx
adox r11, r14
mov rdx, r13
mulx r12, r13, [ rsi + 0x18 ]
adcx r15, r13
adcx r12, r11
xchg rdx, rdi
mulx rbx, r14, [ rsi + 0x40 ]
mov rdx, r10
xor r11, r11
adox rdx, [ rsp + 0x188 ]
adox rcx, [ rsp + 0x120 ]
adcx rdx, [ rsp + 0x130 ]
adcx rcx, [ rsp + 0x128 ]
xchg rdx, r8
mulx r13, r10, [ rsi + 0x38 ]
xor rdx, rdx
adox r14, r10
adox r13, rbx
adcx r14, [ rsp + 0x108 ]
adcx r13, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x0 ]
mulx rbx, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1a0 ], r13
mulx r13, r10, rdi
test al, al
adox r8, r10
adox r13, rcx
adcx r15, [ rsp + 0x20 ]
adcx r12, [ rsp - 0x18 ]
xor rdx, rdx
adox r15, [ rsp + 0x150 ]
adox r12, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x28 ]
mulx r10, rcx, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a8 ], r14
mov [ rsp + 0x1b0 ], r10
mulx r10, r14, r9
mov rdx, rbp
mov [ rsp + 0x1b8 ], rcx
mulx rcx, rbp, [ rsi + 0x10 ]
adcx r15, r11
adcx rbx, r12
test al, al
adox r8, r14
adox r10, r13
xchg rdx, rdi
mulx r13, r11, [ rsi + 0x40 ]
adcx r8, rbp
adcx rcx, r10
mov rdx, [ rsp + 0x178 ]
test al, al
adox rdx, [ rsp + 0x180 ]
mov r12, [ rsp + 0x170 ]
adox r12, [ rsp + 0x168 ]
adcx rdx, [ rsp + 0x80 ]
adcx r12, [ rsp + 0x78 ]
xchg rdx, r9
mulx rbp, r14, [ rsi + 0x28 ]
test al, al
adox r9, r14
adox rbp, r12
mov r10, 0x3a 
bzhi r12, r15, r10
adox r9, [ rsp + 0x118 ]
adox rbp, [ rsp + 0x110 ]
mov r14, [ rsp + 0x1b8 ]
mov r10, r14
mov [ rsp + 0x1c0 ], r12
xor r12, r12
adox r10, [ rsp + 0x1a8 ]
mov [ rsp + 0x1c8 ], r13
mov r13, [ rsp + 0x1b0 ]
adox r13, [ rsp + 0x1a0 ]
xchg rdx, rdi
mulx r12, r14, [ rsi + 0x40 ]
adcx r8, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov [ rsp + 0x1d0 ], r11
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1d8 ], r13
mov [ rsp + 0x1e0 ], r10
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1e8 ], r12
mov [ rsp + 0x1f0 ], r14
mulx r14, r12, [ rsi + 0x0 ]
test al, al
adox r9, r13
adox r10, rbp
adcx r8, r12
adcx r14, rcx
shrd r15, rbx, 58
shr rbx, 58
mov rdx, [ rsp + 0x1f0 ]
add rdx, [ rsp + 0x8 ]
mov rbp, [ rsp + 0x1e8 ]
adcx rbp, [ rsp + 0x0 ]
mov rcx, [ rsp + 0x18 ]
mov r13, rcx
add r13, [ rsp + 0x1e0 ]
mov r12, [ rsp + 0x10 ]
adcx r12, [ rsp + 0x1d8 ]
test al, al
adox r13, [ rsp + 0x148 ]
adox r12, [ rsp + 0x140 ]
adcx r8, r15
adcx rbx, r14
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r14, [ rax + 0x10 ]
mov rdx, r11
mov [ rsp + 0x1f8 ], r10
mulx r10, r11, [ rsi + 0x28 ]
mov [ rsp + 0x200 ], r9
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x208 ], r10
mov [ rsp + 0x210 ], r11
mulx r11, r10, [ rsi + 0x10 ]
xor rdx, rdx
adox rcx, [ rsp - 0x8 ]
adox rbp, [ rsp - 0x10 ]
adcx r13, r10
adcx r11, r12
xor r12, r12
adox r13, [ rsp + 0x70 ]
adox r11, [ rsp + 0x68 ]
mov rdx, [ rsp + 0x160 ]
adcx rdx, [ rsp + 0x40 ]
mov r10, [ rsp + 0x158 ]
adcx r10, [ rsp + 0x38 ]
mov [ rsp + 0x218 ], rbp
xor rbp, rbp
adox r13, r14
adox r15, r11
mov r12, 0x3ffffffffffffff 
mov r14, r8
and r14, r12
xchg rdx, rdi
mulx rbp, r11, [ rsi + 0x30 ]
adox rdi, r11
adox rbp, r10
adcx rdi, [ rsp + 0x210 ]
adcx rbp, [ rsp + 0x208 ]
mov r10, [ rsp + 0x200 ]
add r10, [ rsp + 0xf8 ]
mov r11, [ rsp + 0x1f8 ]
adcx r11, [ rsp + 0xf0 ]
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x220 ], r14
mov [ rsp + 0x228 ], rcx
mulx rcx, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x230 ], r11
mov [ rsp + 0x238 ], r10
mulx r10, r11, r12
test al, al
adox rdi, r14
adox rcx, rbp
mov rdx, [ rsi + 0x18 ]
mulx r14, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x240 ], r15
mov [ rsp + 0x248 ], r13
mulx r13, r15, r9
adcx rdi, rbp
adcx r14, rcx
mov rdx, r11
add rdx, [ rsp + 0x1d0 ]
adcx r10, [ rsp + 0x1c8 ]
test al, al
adox rdx, r15
adox r13, r10
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbp, rcx, [ rax + 0x0 ]
adcx r11, rcx
adcx rbp, r13
shrd r8, rbx, 58
shr rbx, 58
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, [ rax + 0x10 ]
mov rdx, r8
xor r13, r13
adox rdx, [ rsp + 0x248 ]
adox rbx, [ rsp + 0x240 ]
adcx r11, [ rsp + 0x30 ]
adcx rbp, [ rsp + 0x28 ]
mov rcx, rdx
shrd rcx, rbx, 58
shr rbx, 58
xchg rdx, r9
mulx r13, r8, [ rsi + 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x250 ], rbp
mov [ rsp + 0x258 ], r11
mulx r11, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x260 ], r13
mov [ rsp + 0x268 ], r8
mulx r8, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x270 ], rbx
mov [ rsp + 0x278 ], rcx
mulx rcx, rbx, [ rax + 0x18 ]
mov rdx, r12
mov [ rsp + 0x280 ], r8
mulx r8, r12, [ rsi + 0x40 ]
test al, al
adox rdi, r15
adox r10, r14
mov rdx, 0x3a 
bzhi r14, r9, rdx
mov r15, rbp
adox r15, [ rsp + 0x238 ]
adox r11, [ rsp + 0x230 ]
test al, al
adox r15, rbx
adox rcx, r11
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rax + 0x20 ]
adcx rdi, r13
adcx r10, [ rsp + 0x280 ]
test al, al
adox r15, [ rsp + 0x278 ]
adox rcx, [ rsp + 0x270 ]
mov rdx, [ rsi + 0x30 ]
mulx rbx, r13, [ rax + 0x0 ]
adcx rdi, r9
adcx rbp, r10
mov rdx, [ rax + 0x20 ]
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x288 ], r14
mulx r14, r10, [ rax + 0x18 ]
test al, al
adox r12, [ rsp + 0x268 ]
adox r8, [ rsp + 0x260 ]
mov rdx, [ rsp + 0x258 ]
adcx rdx, [ rsp + 0xd8 ]
mov [ rsp + 0x290 ], r14
mov r14, [ rsp + 0x250 ]
adcx r14, [ rsp + 0xd0 ]
test al, al
adox r12, r13
adox rbx, r8
adcx rdx, [ rsp + 0x98 ]
adcx r14, [ rsp + 0x90 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x298 ], r10
mulx r10, r8, [ rax + 0x10 ]
mov rdx, r8
test al, al
adox rdx, [ rsp + 0x228 ]
adox r10, [ rsp + 0x218 ]
mov r8, r15
shrd r8, rcx, 58
shr rcx, 58
mov [ rsp + 0x2a0 ], r10
xor r10, r10
adox rdi, r8
adox rcx, rbp
mov rbp, 0x3a 
bzhi r8, rdi, rbp
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2a8 ], r8
mulx r8, rbp, [ rax + 0x20 ]
mov rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x2b0 ], r10
mov r10, rdx
adox r10, [ rsp + 0x198 ]
mov [ rsp + 0x2b8 ], rbx
mov rbx, [ rsp + 0xa0 ]
adox rbx, [ rsp + 0x190 ]
test al, al
adox r10, rbp
adox r8, rbx
mov rdx, [ rax + 0x28 ]
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x2c0 ], r8
mov [ rsp + 0x2c8 ], r10
mulx r10, r8, [ rsi + 0x28 ]
adcx r13, r11
adcx r9, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, r11, [ rax + 0x10 ]
xor rdx, rdx
adox r13, rbp
adox rbx, r9
adcx r12, r8
adcx r10, [ rsp + 0x2b8 ]
mov rbp, [ rsp + 0x298 ]
mov r8, rbp
add r8, [ rsp + 0x2b0 ]
mov r9, [ rsp + 0x290 ]
adcx r9, [ rsp + 0x2a0 ]
add r12, r11
adcx r14, r10
shrd rdi, rcx, 58
shr rcx, 58
xor rbp, rbp
adox r8, [ rsp + 0x50 ]
adox r9, [ rsp + 0x48 ]
adcx r13, rdi
adcx rcx, rbx
mov rdx, [ rax + 0x28 ]
mulx rbx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r10, [ rax + 0x28 ]
mov rdx, 0x3ffffffffffffff 
mov rbp, r13
and rbp, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2d0 ], rbp
mov [ rsp + 0x2d8 ], r9
mulx r9, rbp, [ rsi + 0x10 ]
adox r12, [ rsp + 0xc8 ]
adox r14, [ rsp + 0xc0 ]
adcx r12, rbp
adcx r9, r14
test al, al
adox r12, r10
adox rdi, r9
mov rdx, [ rax + 0x40 ]
mulx rbp, r10, [ rsi + 0x0 ]
adcx r12, [ rsp + 0xe8 ]
adcx rdi, [ rsp + 0xe0 ]
mov rdx, r11
add rdx, [ rsp + 0x2c8 ]
adcx rbx, [ rsp + 0x2c0 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rax + 0x38 ]
xor rdx, rdx
adox r11, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2e0 ], rbp
mov [ rsp + 0x2e8 ], r10
mulx r10, rbp, [ rsi + 0x8 ]
adcx r11, r14
adcx r9, rbx
test al, al
adox r8, [ rsp - 0x40 ]
mov rdx, [ rsp - 0x48 ]
adox rdx, [ rsp + 0x2d8 ]
shrd r13, rcx, 58
shr rcx, 58
test al, al
adox r12, r13
adox rcx, rdi
adcx r8, rbp
adcx r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, rdi, [ rax + 0x38 ]
mov rdx, r12
shrd rdx, rcx, 58
shr rcx, 58
mov rbx, 0x3a 
bzhi rbp, r12, rbx
adox r8, rdi
adox r14, r10
add r8, rdx
adcx rcx, r14
xor r13, r13
adox r11, [ rsp + 0x2e8 ]
adox r9, [ rsp + 0x2e0 ]
mov r12, r8
shrd r12, rcx, 58
shr rcx, 58
xor r10, r10
adox r11, r12
adox rcx, r9
mov r13, r11
shrd r13, rcx, 57
shr rcx, 57
xor rdi, rdi
adox r13, [ rsp + 0x1c0 ]
adox rcx, rdi
mov r10, r13
shrd r10, rcx, 58
mov rdx, 0x39 
bzhi r14, r11, rdx
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x40 ], r14
bzhi r12, r13, rbx
mov r11, [ rsp + 0x2d0 ]
mov [ r9 + 0x28 ], r11
add r10, [ rsp + 0x220 ]
mov r11, r10
shr r11, 58
add r11, [ rsp + 0x288 ]
bzhi r13, r15, rbx
mov r15, [ rsp + 0x2a8 ]
mov [ r9 + 0x20 ], r15
mov [ r9 + 0x18 ], r13
mov [ r9 + 0x10 ], r11
bzhi r15, r8, rbx
bzhi r8, r10, rbx
mov [ r9 + 0x8 ], r8
mov [ r9 + 0x0 ], r12
mov [ r9 + 0x30 ], rbp
mov [ r9 + 0x38 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 880
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1092
; seed 3850683982051189 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13628216 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 230870 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.016940588555391257
; number reverted permutation / tried permutation: 48161 / 89843 =53.606%
; number reverted decision / tried decision: 33765 / 90156 =37.452%
; validated in 5.688s
