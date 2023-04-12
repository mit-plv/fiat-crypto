SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 816
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r9
mulx r9, r14, [ rsi + 0x20 ]
test al, al
adox r11, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r14
mulx r14, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r14
mulx r14, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], r15
mulx r15, r10, [ rsi + 0x20 ]
adox r8, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r15
mulx r15, rcx, [ rsi + 0x20 ]
adox r12, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r10
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r14
mulx r14, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r8
mulx r8, r12, rdx
adcx r14, r8
mov rdx, 0x100000001 
mov [ rsp + 0x58 ], r11
mulx r11, r8, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], rax
mulx rax, r11, [ rsi + 0x20 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x68 ], rax
mov [ rsp + 0x70 ], r15
mulx r15, rax, r8
seto dl
mov [ rsp + 0x78 ], rcx
mov rcx, -0x2 
inc rcx
adox r11, r9
adcx rbx, rdi
mov r9, 0xffffffff00000000 
xchg rdx, r8
mulx rcx, rdi, r9
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], r11
mov [ rsp + 0x88 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x90 ], r14
mov [ rsp + 0x98 ], rbp
mulx rbp, r14, r9
seto dl
mov [ rsp + 0xa0 ], rbp
mov rbp, -0x2 
inc rbp
adox rdi, r15
adox r14, rcx
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mulx rbp, rcx, rdx
seto dl
mov [ rsp + 0xa8 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r8, r8b
adox r8, rbp
adox r13, r11
adox r10, rbx
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, [ rsi + 0x0 ]
seto dl
inc rbp
adox rax, r12
adcx r11, [ rsp + 0x98 ]
adox rdi, [ rsp + 0x90 ]
mov al, dl
mov rdx, [ rsi + 0x0 ]
mulx rbp, r12, [ rsi + 0x28 ]
adcx rbx, [ rsp + 0x78 ]
adcx r12, [ rsp + 0x70 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xb0 ], rcx
mov byte [ rsp + 0xb8 ], r15b
mulx r15, rcx, r9
mov r9, 0x0 
adcx rbp, r9
clc
adcx rdi, [ rsp + 0x60 ]
mov r9, 0x100000001 
mov rdx, rdi
mov [ rsp + 0xc0 ], r10
mulx r10, rdi, r9
adox r14, [ rsp + 0x88 ]
mov r10, rcx
setc r9b
clc
mov byte [ rsp + 0xc8 ], al
mov rax, -0x1 
movzx r8, r8b
adcx r8, rax
adcx r10, [ rsp + 0xa0 ]
mov r8, rcx
adcx r8, r15
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r13
mov [ rsp + 0xd8 ], rbp
mulx rbp, r13, rdx
adcx rcx, r15
mov rdx, 0x0 
adcx r15, rdx
adox r10, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], rbp
mulx rbp, r11, [ rsi + 0x0 ]
adox r8, rbx
clc
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx r14, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x50 ]
adcx r8, [ rsp + 0x48 ]
seto bl
inc rdx
adox rbp, [ rsp + 0x40 ]
mov r9, [ rsp + 0x10 ]
adox r9, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
adox r13, [ rsp - 0x20 ]
seto dl
mov [ rsp + 0xf8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbx, bl
adox rbx, r13
adox r12, rcx
mov rcx, 0xffffffff00000000 
xchg rdx, rdi
mulx r13, rbx, rcx
mov rcx, 0xffffffff 
mov [ rsp + 0x100 ], rbp
mov [ rsp + 0x108 ], r11
mulx r11, rbp, rcx
adox r15, [ rsp + 0xd8 ]
adcx r12, [ rsp + 0xd0 ]
setc cl
clc
adcx rbx, r11
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], r15
mov byte [ rsp + 0x118 ], cl
mulx rcx, r15, [ rsi + 0x10 ]
setc dl
clc
mov [ rsp + 0x120 ], r12
mov r12, -0x1 
movzx rdi, dil
adcx rdi, r12
adcx r9, [ rsp + 0xe0 ]
mov rdi, 0xfffffffffffffffe 
xchg rdx, rdi
mov [ rsp + 0x128 ], r9
mulx r9, r12, r11
setc dl
clc
mov [ rsp + 0x130 ], r8
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx r13, r12
setc dil
clc
adcx rbp, rax
adcx rbx, r14
seto bpl
inc r8
adox r15, rbx
adcx r13, r10
setc al
clc
adcx rcx, [ rsp + 0x30 ]
mov r14, 0x100000001 
xchg rdx, r14
mulx r12, r10, r15
mov r12, 0xffffffff00000000 
mov rdx, r12
mulx rbx, r12, r10
mov r8, 0xffffffff 
mov rdx, r10
mov byte [ rsp + 0x138 ], bpl
mulx rbp, r10, r8
mov r8, 0xfffffffffffffffe 
mov byte [ rsp + 0x140 ], r14b
mov [ rsp + 0x148 ], rbx
mulx rbx, r14, r8
mov r8, 0xffffffffffffffff 
mov [ rsp + 0x150 ], rbx
mov [ rsp + 0x158 ], r14
mulx r14, rbx, r8
adox rcx, r13
mov rdx, r8
mulx r13, r8, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r14
mulx r14, r11, rdx
adcx r11, [ rsp + 0x28 ]
adcx r14, [ rsp - 0x28 ]
seto dl
mov [ rsp + 0x168 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rdi, dil
adox rdi, r14
adox r9, r8
setc dil
clc
movzx rax, al
adcx rax, r14
adcx r9, [ rsp + 0x130 ]
mov rax, r8
adox rax, r13
mov r14b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], r11
mov [ rsp + 0x178 ], r9
mulx r9, r11, [ rsi + 0x10 ]
adox r8, r13
seto dl
mov byte [ rsp + 0x180 ], r14b
mov r14, 0x0 
dec r14
movzx rdi, dil
adox rdi, r14
adox r11, [ rsp - 0x38 ]
movzx rdi, dl
lea rdi, [ rdi + r13 ]
adcx rax, [ rsp + 0x120 ]
seto r13b
inc r14
adox r10, r15
seto r10b
mov r15, -0x3 
inc r15
adox r12, rbp
mov rbp, [ rsp + 0x148 ]
adox rbp, [ rsp + 0x158 ]
seto dl
dec r14
movzx r10, r10b
adox r10, r14
adox rcx, r12
seto r10b
inc r14
adox rcx, [ rsp + 0x108 ]
mov r12, 0x100000001 
xchg rdx, rcx
mulx r15, r14, r12
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x188 ], r11
mulx r11, r12, [ rsi + 0x10 ]
mov rdx, rbx
mov [ rsp + 0x190 ], r11
setc r11b
clc
mov [ rsp + 0x198 ], rax
mov rax, -0x1 
movzx rcx, cl
adcx rcx, rax
adcx rdx, [ rsp + 0x150 ]
mov rcx, 0xffffffff00000000 
xchg rdx, rcx
mov [ rsp + 0x1a0 ], rcx
mulx rcx, rax, r14
mov rdx, rbx
adcx rdx, [ rsp + 0x160 ]
mov [ rsp + 0x1a8 ], rcx
movzx rcx, byte [ rsp + 0xc8 ]
mov [ rsp + 0x1b0 ], rdx
mov rdx, [ rsp + 0x38 ]
lea rcx, [ rcx + rdx ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x1b8 ], rax
seto al
mov [ rsp + 0x1c0 ], rbp
movzx rbp, byte [ rsp + 0x140 ]
mov byte [ rsp + 0x1c8 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox rbp, r10
adox rdx, [ rsp + 0x100 ]
setc bpl
clc
movzx r13, r13b
adcx r13, r10
adcx r9, r12
seto r13b
inc r10
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox rbx, [ rsp + 0x160 ]
mov rbp, [ rsp + 0x110 ]
setc r10b
movzx r12, byte [ rsp + 0x118 ]
clc
mov byte [ rsp + 0x1d0 ], r13b
mov r13, -0x1 
adcx r12, r13
adcx rbp, [ rsp + 0xc0 ]
movzx r12, byte [ rsp + 0x138 ]
adcx r12, rcx
setc cl
clc
movzx r11, r11b
adcx r11, r13
adcx rbp, r8
adcx rdi, r12
movzx r8, cl
mov r11, 0x0 
adcx r8, r11
mov rcx, [ rsp + 0x170 ]
movzx r12, byte [ rsp + 0x180 ]
clc
adcx r12, r13
adcx rcx, [ rsp + 0x178 ]
seto r12b
movzx r11, byte [ rsp + 0x1c8 ]
inc r13
mov r13, -0x1 
adox r11, r13
adox rcx, [ rsp + 0x1c0 ]
mov r11, [ rsp + 0x198 ]
adcx r11, [ rsp + 0x168 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1d8 ], rbx
mov byte [ rsp + 0x1e0 ], r12b
mulx r12, rbx, [ rsi + 0x20 ]
adcx rbp, [ rsp + 0x188 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1e8 ], r12
mov [ rsp + 0x1f0 ], rbx
mulx rbx, r12, r14
adcx r9, rdi
movzx rdi, r10b
mov rdx, [ rsp + 0x190 ]
lea rdi, [ rdi + rdx ]
adox r11, [ rsp + 0x1a0 ]
setc dl
clc
adcx rbx, [ rsp + 0x1b8 ]
adox rbp, [ rsp + 0x1b0 ]
mov r10, 0xfffffffffffffffe 
xchg rdx, r14
mov [ rsp + 0x1f8 ], rbx
mov [ rsp + 0x200 ], r12
mulx r12, rbx, r10
seto r10b
mov [ rsp + 0x208 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox r8, rdi
adcx rbx, [ rsp + 0x1a8 ]
mov r14, 0xffffffffffffffff 
mulx r13, rdi, r14
mov rdx, rdi
adcx rdx, r12
mov r12, rdi
adcx r12, r13
seto r14b
mov [ rsp + 0x210 ], r12
mov r12, 0x0 
dec r12
movzx rax, al
adox rax, r12
adox rcx, [ rsp + 0xf0 ]
adox r11, [ rsp + 0xe8 ]
adox rbp, [ rsp + 0xf8 ]
movzx rax, byte [ rsp + 0x1e0 ]
mov r12, [ rsp + 0x160 ]
lea rax, [ rax + r12 ]
setc r12b
clc
mov [ rsp + 0x218 ], rdx
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx r9, [ rsp + 0x1d8 ]
adox r9, [ rsp + 0x128 ]
adcx rax, r8
adox rax, [ rsp + 0x208 ]
movzx r10, r14b
mov r8, 0x0 
adcx r10, r8
clc
adcx r15, [ rsp + 0x200 ]
adcx rcx, [ rsp + 0x1f8 ]
seto r15b
mov r14, -0x3 
inc r14
adox rcx, [ rsp - 0x30 ]
mov r8, [ rsp + 0x68 ]
seto r14b
movzx rdx, byte [ rsp + 0xb8 ]
mov [ rsp + 0x220 ], rax
mov rax, 0x0 
dec rax
adox rdx, rax
adox r8, [ rsp + 0x1f0 ]
mov rdx, [ rsp + 0x1e8 ]
adox rdx, [ rsp - 0x40 ]
mov rax, 0x100000001 
xchg rdx, rcx
mov byte [ rsp + 0x228 ], r12b
mov [ rsp + 0x230 ], r10
mulx r10, r12, rax
adcx rbx, r11
seto r10b
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r14, r14b
adox r14, r11
adox rbx, [ rsp + 0x80 ]
mov r14, 0xffffffff00000000 
xchg rdx, r14
mulx rax, r11, r12
mov rdx, 0xffffffff 
mov [ rsp + 0x238 ], rbx
mov [ rsp + 0x240 ], rax
mulx rax, rbx, r12
adcx rbp, [ rsp + 0x218 ]
adox r8, rbp
movzx rbp, byte [ rsp + 0x1d0 ]
mov rdx, [ rsp - 0x8 ]
lea rbp, [ rbp + rdx ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x248 ], r8
mov [ rsp + 0x250 ], r11
mulx r11, r8, rdx
adcx r9, [ rsp + 0x210 ]
adox rcx, r9
setc dl
clc
mov r9, -0x1 
movzx r15, r15b
adcx r15, r9
adcx rbp, [ rsp + 0x230 ]
mov r15, r13
setc r9b
mov [ rsp + 0x258 ], rcx
movzx rcx, byte [ rsp + 0x228 ]
clc
mov [ rsp + 0x260 ], rax
mov rax, -0x1 
adcx rcx, rax
adcx r15, rdi
mov rdi, 0x0 
adcx r13, rdi
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mulx rax, rdi, [ rsi + 0x28 ]
clc
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx r8, [ rsp - 0x48 ]
adcx rdi, r11
setc r10b
clc
movzx rcx, cl
adcx rcx, rdx
adcx r15, [ rsp + 0x220 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rcx, r11, r12
adcx r13, rbp
movzx rbp, r9b
mov rdx, 0x0 
adcx rbp, rdx
adox r8, r15
adox rdi, r13
mov rdx, [ rsi + 0x8 ]
mulx r15, r9, [ rsi + 0x28 ]
clc
adcx rbx, r14
mov rdx, [ rsp + 0x260 ]
setc bl
clc
adcx rdx, [ rsp + 0x250 ]
mov r14, 0xfffffffffffffffe 
xchg rdx, r12
mov [ rsp + 0x268 ], rdi
mulx rdi, r13, r14
adcx r13, [ rsp + 0x240 ]
mov rdx, r11
adcx rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x270 ], rbp
mulx rbp, r14, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x278 ], rax
mov rax, 0x0 
dec rax
movzx rbx, bl
adox rbx, rax
adox r12, [ rsp + 0x238 ]
mov rbx, r11
adcx rbx, rcx
seto al
mov byte [ rsp + 0x280 ], dl
mov rdx, -0x2 
inc rdx
adox r14, r12
seto r12b
inc rdx
adox r9, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x288 ], r14
mulx r14, rbp, [ rsi + 0x10 ]
adox rbp, r15
setc dl
clc
mov r15, -0x1 
movzx rax, al
adcx rax, r15
adcx r13, [ rsp + 0x248 ]
adox r14, [ rsp - 0x10 ]
adcx rdi, [ rsp + 0x258 ]
adcx rbx, r8
seto r8b
inc r15
mov rax, -0x1 
movzx r12, r12b
adox r12, rax
adox r13, r9
adox rbp, rdi
adox r14, rbx
movzx r12, r10b
mov r9, [ rsp + 0x278 ]
lea r12, [ r12 + r9 ]
seto r9b
movzx r10, byte [ rsp + 0x280 ]
dec r15
adox r10, r15
adox r12, [ rsp + 0x270 ]
mov rax, 0x100000001 
xchg rdx, rax
mulx rdi, r10, [ rsp + 0x288 ]
mov rdi, 0xffffffff 
mov rdx, r10
mulx rbx, r10, rdi
mov r15, rcx
seto dil
mov [ rsp + 0x290 ], r14
mov r14, 0x0 
dec r14
movzx rax, al
adox rax, r14
adox r15, r11
mov r11, 0x0 
adox rcx, r11
adcx r15, [ rsp + 0x268 ]
adcx rcx, r12
movzx rax, dil
adc rax, 0x0
mov r12, [ rsp - 0x18 ]
add r8b, 0x7F
adox r12, [ rsp + 0x20 ]
movzx r9, r9b
adcx r9, r14
adcx r15, r12
mov r8, [ rsp + 0x18 ]
adox r8, [ rsp + 0xb0 ]
mov r9, [ rsp + 0xa8 ]
adox r9, r11
mov rdi, 0xffffffff00000000 
mulx r11, r12, rdi
mov r14, 0xfffffffffffffffe 
mov [ rsp + 0x298 ], r9
mulx r9, rdi, r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x2a0 ], rax
mov [ rsp + 0x2a8 ], r15
mulx r15, rax, r14
adcx r8, rcx
mov rdx, -0x2 
inc rdx
adox r12, rbx
adox rdi, r11
mov rbx, rax
adox rbx, r9
mov rcx, rax
adox rcx, r15
setc r11b
clc
adcx r10, [ rsp + 0x288 ]
adcx r12, r13
adcx rdi, rbp
adox rax, r15
adcx rbx, [ rsp + 0x290 ]
adcx rcx, [ rsp + 0x2a8 ]
setc r10b
seto r13b
mov rbp, r12
mov r9, 0xffffffff 
sub rbp, r9
mov rdx, rdi
mov r9, 0xffffffff00000000 
sbb rdx, r9
mov r9, [ rsp + 0x298 ]
mov r14, 0x0 
dec r14
movzx r11, r11b
adox r11, r14
adox r9, [ rsp + 0x2a0 ]
movzx r11, r13b
lea r11, [ r11 + r15 ]
seto r15b
inc r14
mov r13, -0x1 
movzx r10, r10b
adox r10, r13
adox r8, rax
adox r11, r9
movzx rax, r15b
adox rax, r14
mov r10, rbx
mov r9, 0xfffffffffffffffe 
sbb r10, r9
mov r15, rcx
mov r14, 0xffffffffffffffff 
sbb r15, r14
mov r13, r8
sbb r13, r14
mov r9, r11
sbb r9, r14
sbb rax, 0x00000000
cmovc r15, rcx
cmovc r13, r8
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x20 ], r13
cmovc rdx, rdi
cmovc r10, rbx
cmovc r9, r11
mov [ rax + 0x10 ], r10
cmovc rbp, r12
mov [ rax + 0x0 ], rbp
mov [ rax + 0x18 ], r15
mov [ rax + 0x28 ], r9
mov [ rax + 0x8 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 816
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0830
; seed 4108989882272310 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9928235 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=42, initial num_batches=31): 253210 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025504029668918998
; number reverted permutation / tried permutation: 57893 / 89790 =64.476%
; number reverted decision / tried decision: 47019 / 90209 =52.122%
; validated in 38.293s
