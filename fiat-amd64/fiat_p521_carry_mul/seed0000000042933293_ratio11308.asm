SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 792
mov rax, [ rdx + 0x20 ]
lea r10, [rax + rax]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rax + 0x38 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
mov rdx, 0x1 
mov [ rsp - 0x78 ], rbp
shlx rbp, [ rax + 0x40 ], rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rbp
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x40 ], r14
lea r14, [rdx + rdx]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r11
mulx r11, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rcx
mulx rcx, r11, r14
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x18 ], r9
lea r9, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], r13
mulx r13, r8, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], r15
mulx r15, r12, [ rax + 0x20 ]
mov rdx, rbp
mov [ rsp + 0x10 ], r15
mulx r15, rbp, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], r15
mulx r15, rdi, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], rbp
mov [ rsp + 0x38 ], rcx
mulx rcx, rbp, [ rax + 0x18 ]
mov rdx, rbx
mov [ rsp + 0x40 ], rcx
mulx rcx, rbx, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r11
mulx r11, rbp, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], rdi
mulx rdi, r15, r12
mov rdx, 0x1 
mov [ rsp + 0x68 ], rdi
shlx rdi, [ rax + 0x38 ], rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x70 ], r15
mov [ rsp + 0x78 ], rcx
mulx rcx, r15, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], r15
mulx r15, rcx, rdi
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x90 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], rbx
mulx rbx, rcx, rdi
test al, al
adox rbp, r8
adox r13, r11
mov rdx, rdi
mulx r8, rdi, [ rsi + 0x10 ]
mov r11, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], rbp
mulx rbp, r13, r15
mov rdx, r15
mov [ rsp + 0xb8 ], rbx
mulx rbx, r15, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], rcx
mov rcx, [ rax + 0x10 ]
mov [ rsp + 0xc8 ], r8
lea r8, [rcx + rcx]
xchg rdx, r8
mov [ rsp + 0xd0 ], rdi
mulx rdi, rcx, [ rsi + 0x38 ]
mov [ rsp + 0xd8 ], rbp
mov rbp, rcx
adcx rbp, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x78 ]
xor rcx, rcx
adox rbp, r15
adox rbx, rdi
mov r15, rdx
mov rdx, [ rsi + 0x38 ]
mulx rcx, rdi, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rbp
mulx rbp, rbx, [ rsi + 0x38 ]
adcx r13, rdi
adcx rcx, [ rsp + 0xd8 ]
mov rdx, r14
mulx rdi, r14, [ rsi + 0x38 ]
mov [ rsp + 0xf0 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], rdi
mulx rdi, rbx, r8
mov rdx, r15
mulx r8, r15, [ rsi + 0x40 ]
xor rdx, rdx
adox r15, rbx
adox rdi, r8
mov rdx, [ rsi + 0x30 ]
mulx r8, rbx, r10
adcx r15, rbx
adcx r8, rdi
mov rdx, [ rsi + 0x20 ]
mulx rbx, rdi, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], rdi
mulx rdi, rbx, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r8
mulx r8, r10, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], r15
mov [ rsp + 0x128 ], r14
mulx r14, r15, r9
mov rdx, r9
mov [ rsp + 0x130 ], r14
mulx r14, r9, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], r15
mov r15, rbx
test al, al
adox r15, [ rsp + 0xe8 ]
adox rdi, [ rsp + 0xe0 ]
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], r8
mov [ rsp + 0x148 ], r10
mulx r10, r8, r12
adcx r15, [ rsp + 0x60 ]
adcx rdi, [ rsp + 0x58 ]
test al, al
adox r15, [ rsp + 0x50 ]
adox rdi, [ rsp + 0x38 ]
adcx r15, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0xc8 ]
test al, al
adox r13, r9
adox r14, rcx
mov rdx, rbp
mulx rcx, rbp, [ rsi + 0x20 ]
adcx r15, r8
adcx r10, rdi
test al, al
adox r13, [ rsp + 0x148 ]
adox r14, [ rsp + 0x140 ]
xchg rdx, rbx
mulx r8, r9, [ rsi + 0x40 ]
adcx r9, [ rsp + 0x128 ]
adcx r8, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r14
mulx r14, rdi, [ rax + 0x0 ]
test al, al
adox r9, [ rsp + 0x98 ]
adox r8, [ rsp + 0x90 ]
mov rdx, [ rsp + 0x138 ]
mov [ rsp + 0x158 ], r8
mov r8, rdx
adcx r8, [ rsp + 0x120 ]
mov [ rsp + 0x160 ], r9
mov r9, [ rsp + 0x130 ]
adcx r9, [ rsp + 0x118 ]
add r8, rbp
adcx rcx, r9
xor rdx, rdx
adox r15, rdi
adox r14, r10
mov rbp, r15
shrd rbp, r14, 58
shr r14, 58
mov rdx, [ rax + 0x0 ]
mulx rdi, r10, [ rsi + 0x8 ]
test al, al
adox r8, [ rsp + 0xc0 ]
adox rcx, [ rsp + 0xb8 ]
adcx r8, [ rsp + 0x30 ]
adcx rcx, [ rsp + 0x28 ]
test al, al
adox r8, r10
adox rdi, rcx
mov rdx, [ rsi + 0x0 ]
mulx r10, r9, [ rax + 0x8 ]
mov rdx, rbx
mulx rcx, rbx, [ rsi + 0x30 ]
mov [ rsp + 0x168 ], r13
mov r13, rbx
adcx r13, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0xa8 ]
xor rbx, rbx
adox r8, r9
adox r10, rdi
adcx r8, rbp
adcx r14, r10
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mulx r9, rdi, r11
xor rdx, rdx
adox r13, rdi
adox r9, rcx
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbx, r12
mov rdx, r8
shrd rdx, r14, 58
shr r14, 58
mov r10, 0x3a 
bzhi rdi, r15, r10
xchg rdx, r11
mulx r10, r15, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x178 ], r14
mov [ rsp + 0x180 ], r11
mulx r11, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r11
mov [ rsp + 0x190 ], r14
mulx r14, r11, [ rax + 0x0 ]
mov rdx, 0x3ffffffffffffff 
and r8, rdx
adox r13, rbx
adox rcx, r9
mov rdx, [ rsi + 0x0 ]
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, r15
adcx rdx, [ rsp + 0x168 ]
adcx r10, [ rsp + 0x150 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], r8
mov [ rsp + 0x1a0 ], rbx
mulx rbx, r8, [ rax + 0x0 ]
add r13, r11
adcx r14, rcx
test al, al
adox r15, [ rsp + 0x70 ]
adox r10, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, r12
adcx r15, r8
adcx rbx, r10
mov rdx, [ rsi + 0x20 ]
mulx r10, r8, [ rax + 0x0 ]
mov rdx, r11
mov [ rsp + 0x1a8 ], r14
xor r14, r14
adox rdx, [ rsp + 0x160 ]
adox rcx, [ rsp + 0x158 ]
adcx r15, [ rsp + 0x190 ]
adcx rbx, [ rsp + 0x188 ]
test al, al
adox r15, r9
adox rbx, [ rsp + 0x1a0 ]
adcx r15, [ rsp + 0x180 ]
adcx rbx, [ rsp + 0x178 ]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r11, [ rax + 0x10 ]
mov rdx, r15
shrd rdx, rbx, 58
shr rbx, 58
mov [ rsp + 0x1b0 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1b8 ], r14
mov [ rsp + 0x1c0 ], r11
mulx r11, r14, [ rsi + 0x18 ]
mov rdx, r12
mov [ rsp + 0x1c8 ], rbx
mulx rbx, r12, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1d0 ], rbx
mov [ rsp + 0x1d8 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1e0 ], r13
mov [ rsp + 0x1e8 ], r12
mulx r12, r13, rdi
add r9, r8
adcx r10, rcx
mov rdx, [ rax + 0x0 ]
mulx rcx, r8, [ rsi + 0x30 ]
xor rdx, rdx
adox r9, r14
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r14, [ rax + 0x18 ]
adcx r13, [ rsp + 0x88 ]
adcx r12, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x1f0 ], r11
mov [ rsp + 0x1f8 ], r9
mulx r9, r11, rbp
xor rdx, rdx
adox r13, r8
adox rcx, r12
mov rdx, rdi
mulx rbp, rdi, [ rsi + 0x38 ]
mov rdx, rbx
adcx rdx, [ rsp + 0x1e0 ]
mov r8, [ rsp + 0x1e8 ]
adcx r8, [ rsp + 0x1a8 ]
xor rbx, rbx
adox r11, rdi
adox rbp, r9
mov r12, [ rsp + 0xf8 ]
mov r9, r12
adcx r9, [ rsp + 0x20 ]
mov rdi, [ rsp + 0xf0 ]
adcx rdi, [ rsp + 0x8 ]
test al, al
adox rdx, [ rsp + 0x1c0 ]
adox r8, [ rsp + 0x1b8 ]
adcx r11, [ rsp + 0x1d8 ]
adcx rbp, [ rsp + 0x1d0 ]
test al, al
adox rdx, r14
adox r10, r8
adcx rdx, [ rsp + 0x1c8 ]
adcx r10, [ rsp + 0x1b0 ]
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x200 ], rcx
mulx rcx, rbx, [ rax + 0x8 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x208 ], r13
mov r13, r12
and r13, rdx
shrd r12, r10, 58
shr r10, 58
test al, al
adox r9, r14
adox r8, rdi
mov rdx, [ rsi + 0x28 ]
mulx r14, rdi, [ rax + 0x10 ]
adcx r9, rdi
adcx r14, r8
mov rdx, [ rax + 0x0 ]
mulx rdi, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x210 ], r13
mov [ rsp + 0x218 ], r10
mulx r10, r13, [ rsi + 0x20 ]
test al, al
adox r11, r8
adox rdi, rbp
adcx r11, rbx
adcx rcx, rdi
xor rdx, rdx
adox r9, r13
adox r10, r14
adcx r11, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, rbp, [ rax + 0x10 ]
mov rdx, rbp
add rdx, [ rsp + 0x1f8 ]
adcx rbx, [ rsp + 0x1f0 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r8, [ rax + 0x18 ]
xor rdx, rdx
adox r11, r8
adox r13, rcx
mov rdx, [ rsi + 0x28 ]
mulx rcx, rdi, [ rax + 0x8 ]
adcx r11, [ rsp + 0x18 ]
adcx r13, [ rsp + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rbp, [ rsi + 0x18 ]
add r11, [ rsp - 0x10 ]
adcx r13, [ rsp - 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x220 ], r8
mov [ rsp + 0x228 ], rbp
mulx rbp, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x40 ]
adcx r14, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x230 ], rbp
mov [ rsp + 0x238 ], r8
mulx r8, rbp, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x240 ], r8
mov [ rsp + 0x248 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
add r14, r12
adcx rbx, [ rsp + 0x218 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x250 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x258 ], rbp
mov rbp, r14
and rbp, rdx
shrd r14, rbx, 58
shr rbx, 58
mov rdx, rdi
add rdx, [ rsp + 0x208 ]
adcx rcx, [ rsp + 0x200 ]
xor rdi, rdi
adox r11, r14
adox rbx, r13
adcx rdx, [ rsp + 0x110 ]
adcx rcx, [ rsp + 0x108 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x260 ], rbp
mov [ rsp + 0x268 ], r12
mulx r12, rbp, [ rax + 0x20 ]
xor rdx, rdx
adox r9, r14
adox rdi, r10
adcx r13, [ rsp + 0x228 ]
adcx rcx, [ rsp + 0x220 ]
add r13, rbp
adcx r12, rcx
add r13, r8
adcx r12, [ rsp + 0x250 ]
xor r10, r10
adox r13, [ rsp + 0x248 ]
adox r12, [ rsp + 0x240 ]
mov rdx, [ rsi + 0x30 ]
mulx r14, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x30 ]
mulx rcx, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x270 ], r14
mulx r14, r10, [ rsi + 0x20 ]
adcx r9, [ rsp + 0x238 ]
adcx rdi, [ rsp + 0x230 ]
mov rdx, r11
shrd rdx, rbx, 58
shr rbx, 58
test al, al
adox r13, rdx
adox rbx, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x278 ], r14
mulx r14, r12, [ rax + 0x18 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x280 ], r10
mov r10, r13
and r10, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x288 ], r14
mov [ rsp + 0x290 ], r12
mulx r12, r14, [ rsi + 0x40 ]
shrd r13, rbx, 58
shr rbx, 58
test al, al
adox r9, rbp
adox rcx, rdi
adcx r9, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, [ rax + 0x30 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], r10
test al, al
adox r9, r13
adox rbx, rcx
mov r10, r9
shrd r10, rbx, 58
shr rbx, 58
add r14, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
xor r13, r13
adox r14, r8
adox r12, [ rsp + 0x270 ]
adcx r14, [ rsp + 0x290 ]
adcx r12, [ rsp + 0x288 ]
test al, al
adox r14, [ rsp + 0x280 ]
adox r12, [ rsp + 0x278 ]
mov r8, 0x3ffffffffffffff 
and r9, r8
adox r14, [ rsp + 0x268 ]
adox r12, [ rsp + 0x258 ]
adcx r14, rbp
adcx rdi, r12
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ rax + 0x38 ]
add r14, rbp
adcx r12, rdi
and r15, r8
mov rdx, [ rax + 0x40 ]
mulx rbp, rdi, [ rsi + 0x0 ]
adox r14, rdi
adox rbp, r12
adcx r14, r10
adcx rbx, rbp
mov rdx, 0x39 
bzhi r10, r14, rdx
shrd r14, rbx, 57
shr rbx, 57
add r14, [ rsp + 0x170 ]
adc rbx, 0x0
mov r12, r14
shrd r12, rbx, 58
add r12, [ rsp + 0x198 ]
mov rdi, r12
and rdi, r8
mov [ rcx + 0x40 ], r10
and r14, r8
and r11, r8
shr r12, 58
mov [ rcx + 0x28 ], r11
lea r12, [ r12 + r15 ]
mov r15, [ rsp + 0x260 ]
mov [ rcx + 0x20 ], r15
mov [ rcx + 0x10 ], r12
mov [ rcx + 0x38 ], r9
mov r15, [ rsp + 0x210 ]
mov [ rcx + 0x18 ], r15
mov [ rcx + 0x8 ], rdi
mov [ rcx + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 792
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1308
; seed 1693687583303748 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7155615 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=73, initial num_batches=31): 147048 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020550015617106288
; number reverted permutation / tried permutation: 59789 / 89996 =66.435%
; number reverted decision / tried decision: 38967 / 90003 =43.295%
; validated in 4.251s
