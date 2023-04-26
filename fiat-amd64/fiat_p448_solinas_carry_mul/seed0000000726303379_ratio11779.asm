SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 904
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r13
mulx r13, r14, [ rax + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rdi
mulx rdi, r15, [ rax + 0x38 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r15
mulx r15, rdi, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], rcx
mulx rcx, r8, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r8
mov [ rsp + 0x90 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], r8
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xa8 ], r8
mov [ rsp + 0xb0 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, r8
mov [ rsp + 0xc8 ], r9
xor r9, r9
adox rdx, r8
mov [ rsp + 0xd0 ], rbx
mov rbx, rcx
adox rbx, rcx
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], r14
mulx r14, r13, [ rsi + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], rbx
mulx rbx, r9, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, r15
adcx rdx, r10
mov [ rsp + 0x118 ], rbp
mov rbp, r11
adcx rbp, rdi
test al, al
adox rdx, r9
mov [ rsp + 0x120 ], r12
mov r12, rbx
adox r12, rbp
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x128 ], r12
mov [ rsp + 0x130 ], r14
mulx r14, r12, [ rsi + 0x8 ]
adcx r8, r13
adcx rcx, [ rsp + 0x130 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x138 ], r14
mov [ rsp + 0x140 ], r12
mulx r12, r14, [ rsi + 0x28 ]
mov rdx, rbp
test al, al
adox rdx, r15
adox rdi, [ rsp + 0x128 ]
adcx rdx, r10
adcx r11, rdi
test al, al
adox rdx, r9
adox rbx, r11
adcx rbp, [ rsp + 0x120 ]
mov r10, [ rsp + 0x118 ]
mov r9, r10
adcx r9, [ rsp + 0x128 ]
test al, al
adox rbp, [ rsp + 0x110 ]
adox r9, [ rsp + 0x108 ]
adcx rbp, r14
mov r15, r12
adcx r15, r9
mov rdi, r13
test al, al
adox rdi, [ rsp + 0xf0 ]
mov r11, [ rsp + 0x130 ]
adox r11, [ rsp + 0xe8 ]
adcx rdx, [ rsp + 0x120 ]
adcx r10, rbx
xor r13, r13
adox rdx, [ rsp + 0x110 ]
adox r10, [ rsp + 0x108 ]
adcx rdx, r14
adcx r12, r10
mov r14, rdx
mov rdx, [ rax + 0x38 ]
mulx r9, rbx, [ rsi + 0x20 ]
xor rdx, rdx
adox r14, [ rsp + 0xe0 ]
adox r12, [ rsp + 0xd8 ]
mov rdx, [ rax + 0x30 ]
mulx r10, r13, [ rsi + 0x10 ]
adcx r14, [ rsp + 0xc0 ]
adcx r12, [ rsp + 0xb8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r8
mulx r8, rcx, [ rsi + 0x30 ]
add rbp, [ rsp + 0xe0 ]
adcx r15, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], rdi
mulx rdi, r11, [ rax + 0x20 ]
xor rdx, rdx
adox r11, rcx
adox r8, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, rcx, [ rax + 0x0 ]
adcx rbp, [ rsp + 0xc0 ]
adcx r15, [ rsp + 0xb8 ]
add r11, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x68 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x168 ], r15
mov [ rsp + 0x170 ], rbp
mulx rbp, r15, [ rsi + 0x38 ]
xor rdx, rdx
adox r11, rbx
adox r9, r8
mov rdx, [ rax + 0x10 ]
mulx r8, rbx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x178 ], r8
mov [ rsp + 0x180 ], rbx
mulx rbx, r8, [ rsi + 0x30 ]
mov rdx, r11
adcx rdx, rcx
adcx rdi, r9
mov rcx, r15
add rcx, r8
mov [ rsp + 0x188 ], rdi
mov rdi, rbx
adcx rdi, rbp
mov [ rsp + 0x190 ], rdx
mov rdx, rcx
mov [ rsp + 0x198 ], r12
xor r12, r12
adox rdx, r15
adox rbp, rdi
adcx r14, r13
mov r15, r10
adcx r15, [ rsp + 0x198 ]
test al, al
adox rdx, r8
adox rbx, rbp
mov r8, rdx
mov rdx, [ rax + 0x18 ]
mulx r12, rbp, [ rsi + 0x30 ]
adcx r14, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x48 ]
xor rdx, rdx
adox r8, [ rsp + 0x180 ]
adox rbx, [ rsp + 0x178 ]
adcx r8, rbp
mov [ rsp + 0x1a0 ], r15
mov r15, r12
adcx r15, rbx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1a8 ], r14
mulx r14, rbx, [ rsi + 0x28 ]
xor rdx, rdx
adox r8, rbx
mov [ rsp + 0x1b0 ], r12
mov r12, r14
adox r12, r15
mov r15, r13
adcx r15, [ rsp + 0x170 ]
adcx r10, [ rsp + 0x168 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1b8 ], r12
mulx r12, r13, [ rsi + 0x38 ]
test al, al
adox rcx, [ rsp + 0x180 ]
adox rdi, [ rsp + 0x178 ]
adcx r15, [ rsp + 0x50 ]
adcx r10, [ rsp + 0x48 ]
add r11, r13
adcx r12, r9
xor rdx, rdx
adox rcx, rbp
adox rdi, [ rsp + 0x1b0 ]
mov rdx, [ rax + 0x8 ]
mulx rbp, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1c0 ], r10
mulx r10, r13, [ rsi + 0x8 ]
adcx r11, r9
adcx rbp, r12
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, [ rax + 0x20 ]
xor rdx, rdx
adox r11, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
adcx r11, [ rsp + 0xd0 ]
adcx rbp, [ rsp + 0xc8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1c8 ], r15
mov [ rsp + 0x1d0 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x1d8 ], rdi
mov [ rsp + 0x1e0 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r12
adox r9, rbp
adcx r11, [ rsp + 0x10 ]
adcx r9, [ rsp + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx rbp, r12, [ rsi + 0x8 ]
test al, al
adox r11, r13
adox r10, r9
adcx r8, [ rsp - 0x10 ]
mov rdx, [ rsp + 0x1b8 ]
adcx rdx, [ rsp - 0x18 ]
mov r13, [ rsp + 0x1a8 ]
add r13, [ rsp + 0xa0 ]
mov r9, [ rsp + 0x1a0 ]
adcx r9, [ rsp + 0x98 ]
mov [ rsp + 0x1e8 ], rcx
xor rcx, rcx
adox r8, [ rsp + 0x80 ]
adox rdx, [ rsp + 0x78 ]
adcx r13, [ rsp + 0x30 ]
adcx r9, [ rsp + 0x28 ]
mov [ rsp + 0x1f0 ], rdx
xor rdx, rdx
adox r13, [ rsp - 0x20 ]
adox r9, [ rsp - 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1f8 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
adcx r13, r12
adcx rbp, r9
add r11, rdi
adcx r15, r10
mov rdx, [ rsp + 0x1f8 ]
xor rdi, rdi
adox rdx, [ rsp + 0x40 ]
mov r12, [ rsp + 0x1f0 ]
adox r12, [ rsp + 0x38 ]
mov r10, rbx
adcx r10, [ rsp + 0x1e8 ]
adcx r14, [ rsp + 0x1d0 ]
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx rdi, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x200 ], r15
mov [ rsp + 0x208 ], r11
mulx r11, r15, [ rax + 0x20 ]
xor rdx, rdx
adox rbx, rcx
adox r8, r12
mov rdx, [ rax + 0x18 ]
mulx r12, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x210 ], r12
mov [ rsp + 0x218 ], rcx
mulx rcx, r12, [ rsi + 0x8 ]
adcx r10, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x220 ], r14
mov [ rsp + 0x228 ], r10
mulx r10, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x230 ], rbp
mov [ rsp + 0x238 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x240 ], r11
mov [ rsp + 0x248 ], r15
mulx r15, r11, [ rsi + 0x30 ]
mov rdx, r9
test al, al
adox rdx, [ rsp + 0x160 ]
mov [ rsp + 0x250 ], r15
mov r15, rdi
adox r15, [ rsp + 0x158 ]
adcx rdx, [ rsp + 0x100 ]
adcx r15, [ rsp + 0xf8 ]
mov [ rsp + 0x258 ], r11
xor r11, r11
adox rbx, rbp
adox r13, r8
mov r8, [ rsp + 0x190 ]
adcx r8, [ rsp + 0x60 ]
mov rbp, [ rsp + 0x188 ]
adcx rbp, [ rsp + 0x58 ]
mov [ rsp + 0x260 ], r15
xor r15, r15
adox r8, r12
adox rcx, rbp
adcx r8, r14
adcx r10, rcx
mov r11, [ rsp + 0x238 ]
xor r12, r12
adox r11, [ rsp + 0x248 ]
mov r15, [ rsp + 0x230 ]
adox r15, [ rsp + 0x240 ]
mov r14, rdx
mov rdx, [ rax + 0x38 ]
mulx rcx, rbp, [ rsi + 0x18 ]
adcx rbx, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
xor rdx, rdx
adox rbx, [ rsp + 0x1e0 ]
adox r13, [ rsp + 0x1d8 ]
mov r12, r8
shrd r12, r10, 56
test al, al
adox r11, r12
adox r15, rdx
adcx r14, [ rsp + 0xb0 ]
mov r10, [ rsp + 0x260 ]
adcx r10, [ rsp + 0xa8 ]
mov r12, [ rsp + 0x208 ]
mov rdx, [ rsp + 0x200 ]
mov [ rsp + 0x268 ], r13
mov r13, r12
shrd r13, rdx, 56
test al, al
adox r14, rbp
mov rdx, rcx
adox rdx, r10
mov r10, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x270 ], rbx
mov [ rsp + 0x278 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
adcx r14, [ rsp + 0x258 ]
adcx r10, [ rsp + 0x250 ]
mov rdx, r11
mov [ rsp + 0x280 ], r13
xor r13, r13
adox rdx, [ rsp + 0x278 ]
adox r15, r13
mov r11, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x288 ], r15
mulx r15, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x290 ], r11
mov [ rsp + 0x298 ], rbx
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, r11
adcx rdx, [ rsp + 0x1c8 ]
adcx rbx, [ rsp + 0x1c0 ]
test al, al
adox r14, [ rsp + 0x90 ]
adox r10, [ rsp + 0x88 ]
mov r11, rdx
adcx r11, [ rsp + 0x278 ]
adc rbx, 0x0
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2a0 ], rbx
mov [ rsp + 0x2a8 ], r11
mulx r11, rbx, [ rax + 0x30 ]
add r14, [ rsp + 0x20 ]
adcx r10, [ rsp + 0x18 ]
xor rdx, rdx
adox r14, [ rsp + 0x218 ]
adox r10, [ rsp + 0x210 ]
adcx r14, r13
adcx r15, r10
test al, al
adox r14, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
mov r13, [ rsp + 0x2a8 ]
mov r10, [ rsp + 0x2a0 ]
mov rdx, r13
shrd rdx, r10, 56
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2b0 ], r15
mov [ rsp + 0x2b8 ], r14
mulx r14, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2c0 ], r10
mov [ rsp + 0x2c8 ], r14
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, r9
test al, al
adox rdx, [ rsp + 0x150 ]
adox rdi, [ rsp + 0x148 ]
mov r9, rbx
adcx r9, [ rsp + 0x2b8 ]
adcx r11, [ rsp + 0x2b0 ]
mov rbx, [ rsp + 0x228 ]
test al, al
adox rbx, [ rsp + 0x80 ]
mov [ rsp + 0x2d0 ], r11
mov r11, [ rsp + 0x220 ]
adox r11, [ rsp + 0x78 ]
mov [ rsp + 0x2d8 ], r9
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2e0 ], r15
mov [ rsp + 0x2e8 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, 0x38 
mov [ rsp + 0x2f0 ], r9
bzhi r9, r12, rdx
adox rbx, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
test al, al
adox rbx, [ rsp + 0x298 ]
adox r11, [ rsp + 0x280 ]
mov r12, r10
adcx r12, [ rsp + 0x270 ]
adcx r14, [ rsp + 0x268 ]
xor r10, r10
adox r12, r15
adox rdi, r14
mov r15, [ rsp + 0x100 ]
mov r14, r15
adcx r14, [ rsp + 0x2f0 ]
mov rdx, [ rsp + 0xf8 ]
adcx rdx, [ rsp + 0x2e8 ]
xor r15, r15
adox r14, [ rsp + 0xb0 ]
adox rdx, [ rsp + 0xa8 ]
mov r10, [ rsp + 0x290 ]
mov r15, [ rsp + 0x288 ]
mov [ rsp + 0x2f8 ], r11
mov r11, r10
shrd r11, r15, 56
xor r15, r15
adox r12, r11
adox rdi, r15
adcx r14, rbp
adcx rcx, rdx
mov rbp, r12
shrd rbp, rdi, 56
add r14, [ rsp + 0x2e0 ]
adcx rcx, [ rsp + 0x2c8 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0x2d8 ]
mov r11, [ rsp + 0x2d0 ]
adox r11, r15
mov rdi, rdx
shrd rdi, r11, 56
mov rbp, 0x38 
bzhi r11, r13, rbp
adox r14, [ rsp + 0x140 ]
adox rcx, [ rsp + 0x138 ]
lea rdi, [ rdi + r9 ]
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r9, [ rax + 0x8 ]
mov rdx, rdi
shr rdx, 56
xor rbp, rbp
adox rbx, r9
adox r15, [ rsp + 0x2f8 ]
lea r11, [ r11 + rdx ]
mov r9, 0x38 
bzhi rbp, r11, r9
mov [ rsp + 0x300 ], rbp
bzhi rbp, r10, r9
adox rbx, [ rsp + 0x2c0 ]
mov r10, 0x0 
adox r15, r10
bzhi r10, r8, r9
lea rbp, [ rbp + rdx ]
shr r11, 56
bzhi r8, rbx, r9
lea r11, [ r11 + r8 ]
bzhi rdx, rdi, r9
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x10 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], rdi
shrd rbx, r15, 56
add r14, r8
adcx r9, rcx
xor rcx, rcx
adox r14, rbx
adox r9, rcx
mov r15, r14
shrd r15, r9, 56
mov rdi, 0xffffffffffffff 
and r14, rdi
lea r15, [ r15 + r10 ]
mov r10, r15
shr r10, 56
lea r10, [ r10 + rbp ]
mov rbp, r10
shr rbp, 56
and r12, rdi
and r10, rdi
and r13, rdi
mov [ rdx + 0x30 ], r13
mov [ rdx + 0x8 ], r11
and r15, rdi
mov [ rdx + 0x18 ], r15
lea rbp, [ rbp + r12 ]
mov r11, [ rsp + 0x300 ]
mov [ rdx + 0x0 ], r11
mov [ rdx + 0x10 ], r14
mov [ rdx + 0x20 ], r10
mov [ rdx + 0x28 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 904
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1779
; seed 3795717971499456 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5266632 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=104, initial num_batches=31): 123161 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02338515392759547
; number reverted permutation / tried permutation: 51794 / 89870 =57.632%
; number reverted decision / tried decision: 47254 / 90129 =52.429%
; validated in 3.307s
