SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 504
mov rax, [ rdx + 0x40 ]
mov r10, rax
shl r10, 0x1
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
imul rdx, [ rax + 0x30 ], 0x2
mov [ rsp - 0x48 ], r9
mov r9, [ rax + 0x10 ]
mov [ rsp - 0x40 ], r8
lea r8, [r9 + r9]
imul r9, [ rax + 0x18 ], 0x2
mov [ rsp - 0x38 ], rcx
mov rcx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], r14
mulx r14, r11, [ rsi + 0x28 ]
mov rdx, r8
mov [ rsp - 0x20 ], r14
mulx r14, r8, [ rsi + 0x38 ]
mov [ rsp - 0x18 ], r11
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r12
mulx r12, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], r13
mulx r13, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r13
mov [ rsp + 0x18 ], r12
mulx r12, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r13
mulx r13, r12, [ rax + 0x20 ]
imul rdx, [ rax + 0x28 ], 0x2
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], r12
mulx r12, r13, [ rsi + 0x30 ]
mov [ rsp + 0x40 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r13
mulx r13, r12, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r13
mov [ rsp + 0x60 ], r12
mulx r12, r13, [ rsi + 0x28 ]
mov rdx, 0x1 
mov [ rsp + 0x68 ], r12
shlx r12, [ rax + 0x8 ], rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], r13
mov [ rsp + 0x78 ], r9
mulx r9, r13, r10
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x80 ], r9
mov [ rsp + 0x88 ], r13
mulx r13, r9, rbx
mov rdx, r12
mov [ rsp + 0x90 ], rcx
mulx rcx, r12, [ rsi + 0x40 ]
xor rdx, rdx
adox r12, r8
adox r14, rcx
adcx r9, r15
adcx rdi, r13
mov rdx, [ rsi + 0x38 ]
mulx r8, r15, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x40 ]
mulx rcx, r13, rbp
xor rdx, rdx
adox r13, r15
adox r8, rcx
imul r15, [ rax + 0x20 ], 0x2
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x98 ], rdi
mulx rdi, rcx, rbp
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa0 ], r9
mov [ rsp + 0xa8 ], rdi
mulx rdi, r9, rbx
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xb0 ], rcx
mov [ rsp + 0xb8 ], r15
mulx r15, rcx, r11
test al, al
adox r13, r9
adox rdi, r8
mov rdx, [ rsi + 0x38 ]
mulx r8, r11, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], rdi
mulx rdi, r9, [ rsp + 0x78 ]
adcx rcx, r11
adcx r8, r15
add r12, r9
adcx rdi, r14
mov rdx, [ rsi + 0x30 ]
mulx r15, r14, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x28 ]
mulx r9, r11, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], r13
mov [ rsp + 0xd0 ], r8
mulx r8, r13, rbp
test al, al
adox r12, r11
adox r9, rdi
mov rdx, [ rax + 0x28 ]
mulx r11, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r11
mov [ rsp + 0xe0 ], rdi
mulx rdi, r11, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], rdi
mov [ rsp + 0xf0 ], r11
mulx r11, rdi, [ rsp + 0x90 ]
adcx r12, r13
adcx r8, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, [ rsp + 0x90 ]
test al, al
adox r12, rdi
adox r11, r8
mov rdx, rbp
mulx rdi, rbp, [ rsi + 0x28 ]
adcx rcx, r14
adcx r15, [ rsp + 0xd0 ]
add rcx, rbp
adcx rdi, r15
mov rdx, [ rsi + 0x18 ]
mulx r8, r14, rbx
xor rdx, rdx
adox rcx, r13
adox r9, rdi
mov rdx, [ rsi + 0x40 ]
mulx rbp, r13, [ rsp + 0x78 ]
adcx rcx, r14
adcx r8, r9
mov rdx, [ rsi + 0x38 ]
mulx rdi, r15, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x28 ]
mulx r9, r14, [ rsp + 0x90 ]
test al, al
adox r13, r15
adox rdi, rbp
adcx rcx, [ rsp + 0xf0 ]
adcx r8, [ rsp + 0xe8 ]
add r13, [ rsp + 0x50 ]
adcx rdi, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], rcx
mulx rcx, r8, rbx
add r12, r8
adcx rcx, r11
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ rax + 0x0 ]
xor rdx, rdx
adox r13, r14
adox r9, rdi
adcx r13, [ rsp + 0x40 ]
adcx r9, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx rdi, r14, r10
add r12, rbp
adcx r15, rcx
xor rdx, rdx
adox r13, r14
adox rdi, r9
mov rdx, [ rsp + 0xb8 ]
mulx rcx, rbp, [ rsi + 0x40 ]
adcx r12, r11
adcx r8, r15
mov rdx, r12
shrd rdx, r8, 58
shr r8, 58
mov r11, rdx
mov rdx, [ rsi + 0x40 ]
mulx r14, r9, [ rsp + 0x90 ]
mov rdx, [ rsp + 0x90 ]
mov [ rsp + 0x108 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x110 ], r13
mov [ rsp + 0x118 ], r8
mulx r8, r13, rbx
mov rdx, 0x3a 
mov [ rsp + 0x120 ], r11
bzhi r11, r12, rdx
adox r9, r13
adox r8, r14
mov rdx, [ rsi + 0x28 ]
mulx r14, r12, rbx
test al, al
adox rbp, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0xa8 ]
mov rdx, [ rax + 0x0 ]
mulx r13, rbx, [ rsi + 0x28 ]
adcx rbp, r15
adcx rdi, rcx
xor rdx, rdx
adox rbp, r12
adox r14, rdi
mov rdx, [ rsi + 0x8 ]
mulx r12, r15, [ rax + 0x0 ]
adcx r9, [ rsp + 0x88 ]
adcx r8, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, [ rax + 0x8 ]
add r9, rbx
adcx r13, r8
mov rdx, r15
xor rbx, rbx
adox rdx, [ rsp + 0x100 ]
adox r12, [ rsp + 0xf8 ]
adcx rdx, rcx
adcx rdi, r12
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r8, [ rax + 0x0 ]
xor rdx, rdx
adox r15, [ rsp + 0x120 ]
adox rdi, [ rsp + 0x118 ]
mov rdx, [ rsi + 0x20 ]
mulx r12, rbx, r10
adcx rbp, rbx
adcx r12, r14
test al, al
adox rbp, r8
adox rcx, r12
mov rdx, [ rax + 0x28 ]
mulx r8, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r12, rbx, [ rsi + 0x10 ]
adcx rbp, rbx
adcx r12, rcx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], r8
mulx r8, r11, [ rax + 0x10 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x138 ], r14
mov r14, r15
and r14, rdx
adox rbp, rcx
adox rbx, r12
mov rdx, r10
mulx r12, r10, [ rsi + 0x28 ]
adcx r9, [ rsp - 0x10 ]
adcx r13, [ rsp - 0x28 ]
add r9, r11
adcx r8, r13
mov rdx, [ rsi + 0x10 ]
mulx r11, rcx, [ rax + 0x18 ]
xor rdx, rdx
adox r9, rcx
adox r11, r8
adcx r9, [ rsp + 0x38 ]
adcx r11, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, [ rax + 0x18 ]
test al, al
adox rbp, r13
adox r8, rbx
mov rdx, r10
adcx rdx, [ rsp + 0xc8 ]
adcx r12, [ rsp + 0xc0 ]
xor rbx, rbx
adox rdx, [ rsp + 0x18 ]
adox r12, [ rsp + 0x10 ]
adcx r9, [ rsp + 0x138 ]
adcx r11, [ rsp + 0x130 ]
mov r10, [ rsp + 0x110 ]
test al, al
adox r10, [ rsp - 0x30 ]
mov rcx, [ rsp + 0x108 ]
adox rcx, [ rsp - 0x38 ]
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x140 ], r14
mulx r14, rbx, [ rsi + 0x18 ]
adcx r10, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
xor rdx, rdx
adox r10, [ rsp + 0x8 ]
adox rcx, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x148 ], r11
mov [ rsp + 0x150 ], r9
mulx r9, r11, [ rax + 0x0 ]
shrd r15, rdi, 58
shr rdi, 58
xor rdx, rdx
adox r10, r15
adox rdi, rcx
mov rdx, [ rsi + 0x30 ]
mulx r15, rcx, [ rax + 0x10 ]
mov rdx, r10
shrd rdx, rdi, 58
shr rdi, 58
test al, al
adox rbp, rdx
adox rdi, r8
adcx r13, rbx
adcx r14, r12
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x158 ], r15
mulx r15, rbx, [ rax + 0x10 ]
xor rdx, rdx
adox r13, rbx
adox r15, r14
adcx r13, r8
adcx r12, r15
mov r14, 0x3a 
bzhi r8, r10, r14
mov r10, r11
adox r10, [ rsp + 0xa0 ]
adox r9, [ rsp + 0x98 ]
test al, al
adox r10, [ rsp - 0x18 ]
adox r9, [ rsp - 0x20 ]
bzhi r11, rbp, r14
mov rdx, [ rsi + 0x40 ]
mulx r15, rbx, [ rax + 0x0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r11
mov r11, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x160 ], r8
mulx r8, r14, [ rsi + 0x38 ]
adox rbx, r14
adox r8, r15
test al, al
adox r10, [ rsp + 0x28 ]
adox r9, [ rsp + 0x20 ]
adcx rbx, rcx
adcx r8, [ rsp + 0x158 ]
add rbx, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, [ rax + 0x18 ]
test al, al
adox r10, rcx
adox r15, r9
mov rdx, [ rsi + 0x38 ]
mulx r9, r14, [ rax + 0x0 ]
shrd rbp, rdi, 58
shr rdi, 58
mov rdx, [ rsi + 0x0 ]
mulx r11, rcx, [ rax + 0x20 ]
add r13, rcx
adcx r11, r12
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, [ rax + 0x20 ]
xor rdx, rdx
adox r10, r12
adox rcx, r15
adcx r13, rbp
adcx rdi, r11
mov r15, 0x3ffffffffffffff 
mov rbp, r13
and rbp, r15
mov rdx, [ rax + 0x8 ]
mulx r12, r11, [ rsi + 0x30 ]
shrd r13, rdi, 58
shr rdi, 58
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x168 ], rbp
mulx rbp, r15, [ rax + 0x30 ]
add r10, [ rsp + 0xe0 ]
adcx rcx, [ rsp + 0xd8 ]
mov rdx, r14
add rdx, [ rsp + 0x60 ]
adcx r9, [ rsp + 0x58 ]
xor r14, r14
adox r10, r15
adox rbp, rcx
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, rcx, [ rax + 0x28 ]
adcx r15, r11
adcx r12, r9
mov rdx, [ rax + 0x20 ]
mulx r9, r11, [ rsi + 0x20 ]
mov rdx, r13
test al, al
adox rdx, [ rsp + 0x150 ]
adox rdi, [ rsp + 0x148 ]
adcx rbx, r11
adcx r9, r8
mov r8, rdx
shrd r8, rdi, 58
shr rdi, 58
mov r13, 0x3ffffffffffffff 
and rdx, r13
adox rbx, rcx
adox r14, r9
mov rcx, rdx
mov rdx, [ rax + 0x30 ]
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r14
mulx r14, r13, [ rax + 0x10 ]
adcx r15, r13
adcx r14, r12
test al, al
adox r10, r8
adox rdi, rbp
mov rdx, [ rax + 0x18 ]
mulx r12, rbp, [ rsi + 0x20 ]
adcx r15, rbp
adcx r12, r14
mov rdx, [ rax + 0x20 ]
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x28 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r14, [ rax + 0x28 ]
add r15, r8
adcx r13, r12
mov rdx, [ rax + 0x30 ]
mulx r8, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r15, r14
adox rbp, r13
adcx r15, r11
adcx r9, rbp
mov rdx, [ rax + 0x38 ]
mulx r14, r11, [ rsi + 0x0 ]
add r15, r11
adcx r14, r9
mov rdx, r10
shrd rdx, rdi, 58
shr rdi, 58
test al, al
adox r15, rdx
adox rdi, r14
mov r13, r15
shrd r13, rdi, 58
shr rdi, 58
xor rbp, rbp
adox rbx, r12
adox r8, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r12, [ rax + 0x38 ]
adcx rbx, r12
adcx r9, r8
mov rdx, [ rsi + 0x0 ]
mulx r14, r11, [ rax + 0x40 ]
xor rdx, rdx
adox rbx, r11
adox r14, r9
adcx rbx, r13
adcx rdi, r14
mov rbp, 0x1ffffffffffffff 
mov r13, rbx
and r13, rbp
shrd rbx, rdi, 57
shr rdi, 57
test al, al
adox rbx, [ rsp + 0x128 ]
adox rdi, rdx
mov [ rcx + 0x40 ], r13
mov r8, rbx
shrd r8, rdi, 58
add r8, [ rsp + 0x140 ]
mov r12, 0x3ffffffffffffff 
and rbx, r12
mov [ rcx + 0x0 ], rbx
mov r9, r8
shr r9, 58
add r9, [ rsp + 0x160 ]
mov [ rcx + 0x10 ], r9
and r8, r12
mov r11, [ rsp + 0x168 ]
mov [ rcx + 0x20 ], r11
and r15, r12
and r10, r12
mov [ rcx + 0x8 ], r8
mov [ rcx + 0x38 ], r15
mov [ rcx + 0x30 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 504
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3478
; seed 2838907043386657 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6885937 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=53, initial num_batches=31): 137441 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019959665619943952
; number reverted permutation / tried permutation: 65723 / 89804 =73.185%
; number reverted decision / tried decision: 55061 / 90195 =61.047%
; validated in 4.626s
