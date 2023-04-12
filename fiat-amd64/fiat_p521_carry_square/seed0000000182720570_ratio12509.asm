SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 528
mov rax, [ rsi + 0x30 ]
lea r10, [ 4 * rax]
imul rax, [ rsi + 0x28 ], 0x4
imul r11, [ rsi + 0x28 ], 0x2
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, r10
mov rdx, 0x1 
shlx r9, [ rsi + 0x8 ], rdx
mov rdx, r11
mov [ rsp - 0x80 ], rbx
mulx rbx, r11, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x40 ]
mov [ rsp - 0x70 ], r12
mov r12, rbp
shl r12, 0x2
xchg rdx, r10
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
mov rdx, r10
mov [ rsp - 0x48 ], r9
mulx r9, r10, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], r8
mulx r8, r10, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r8
mulx r8, rcx, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r8
mulx r8, rcx, r12
mov rdx, r14
mov [ rsp + 0x8 ], r8
mulx r8, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x10 ], rcx
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rcx
lea rcx, [rdx + rdx]
add r11, r14
adcx r8, rbx
mov rdx, [ rsi + 0x38 ]
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rcx
mulx rcx, r14, rbx
mov rdx, r12
mov [ rsp + 0x28 ], rcx
mulx rcx, r12, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r14
imul r14, [ rsi + 0x38 ], 0x4
xchg rdx, r14
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r11
mulx r11, r8, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], r10
mov [ rsp + 0x50 ], rax
mulx rax, r10, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rax
xor rax, rax
adox r8, r15
adox rdi, r11
mulx r11, r15, [ rsi + 0x18 ]
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r10
mov [ rsp + 0x68 ], r11
mulx r11, r10, r9
mov rdx, rbx
mov [ rsp + 0x70 ], r11
mulx r11, rbx, [ rsi + 0x38 ]
adcx rbx, r12
adcx rcx, r11
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r10
mulx r10, r11, rax
test al, al
adox rbp, r11
adox r10, r13
mov rdx, [ rsi + 0x20 ]
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r13
mulx r13, r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], rbx
mulx rbx, rcx, [ rsp + 0x50 ]
adcx rbp, [ rsp + 0x48 ]
adcx r10, [ rsp - 0x20 ]
add rcx, [ rsp - 0x28 ]
adcx rbx, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], rbp
mulx rbp, r10, rax
xor rdx, rdx
adox r8, r11
adox r13, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, rax, rdx
adcx rcx, r10
adcx rbp, rbx
test al, al
adox rcx, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x18 ]
adcx rcx, rax
adcx rdi, rbp
mov rdx, rcx
shrd rdx, rdi, 58
shr rdi, 58
mov r11, rdx
mov rdx, [ rsp - 0x48 ]
mulx r10, rbx, [ rsi + 0x0 ]
imul rdx, [ rsi + 0x18 ], 0x2
mulx rbp, rax, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], rdi
mov rdi, r15
mov [ rsp + 0xb0 ], r11
xor r11, r11
adox rdi, [ rsp + 0x40 ]
mov [ rsp + 0xb8 ], r10
mov r10, [ rsp + 0x38 ]
adox r10, [ rsp + 0x68 ]
imul r15, [ rsi + 0x30 ], 0x2
mov [ rsp + 0xc0 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], rax
mov [ rsp + 0xd8 ], r10
mulx r10, rax, r15
add r8, r11
adcx rbx, r13
mov rdx, rbp
mulx r13, rbp, [ rsi + 0x0 ]
mov rdx, 0x3ffffffffffffff 
and rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], rcx
mulx rcx, r11, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r10
mov [ rsp + 0xf0 ], rax
mulx rax, r10, r15
adox rdi, [ rsp + 0x10 ]
mov rdx, [ rsp + 0x8 ]
adox rdx, [ rsp + 0xd8 ]
xchg rdx, r15
mov [ rsp + 0xf8 ], rax
mov [ rsp + 0x100 ], r10
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], r10
mov [ rsp + 0x110 ], rax
mulx rax, r10, rdx
mov rdx, [ rsp + 0x90 ]
adcx rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x118 ], rbx
mov rbx, [ rsp + 0x88 ]
adcx rbx, [ rsp + 0xc8 ]
add rdi, [ rsp + 0xc0 ]
adcx r15, [ rsp + 0xb8 ]
mov [ rsp + 0x120 ], r8
mov r8, rdx
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0x128 ], rbx
mov [ rsp + 0x130 ], r13
mulx r13, rbx, [ rsi + 0x0 ]
mov [ rsp + 0x138 ], r8
mov r8, r10
mov [ rsp + 0x140 ], rbp
xor rbp, rbp
adox r8, [ rsp + 0xa0 ]
adox rax, [ rsp + 0x98 ]
adcx rdi, [ rsp + 0xb0 ]
adcx r15, [ rsp + 0xa8 ]
mov r10, rdi
shrd r10, r15, 58
shr r15, 58
mov [ rsp + 0x148 ], rcx
xor rcx, rcx
adox r8, rbx
adox r13, rax
adcx r8, r10
adcx r15, r13
test al, al
adox r11, [ rsp + 0x60 ]
mov rbp, [ rsp + 0x148 ]
adox rbp, [ rsp + 0x58 ]
mulx rax, rbx, [ rsi + 0x8 ]
adcx r11, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
xor rdx, rdx
adox r11, rbx
adox rax, rbp
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, [ rsp + 0x80 ]
mov rdx, 0x3a 
bzhi r13, r8, rdx
shrd r8, r15, 58
shr r15, 58
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, [ rsp + 0x80 ]
xor rdx, rdx
adox r11, [ rsp + 0x140 ]
adox rax, [ rsp + 0x130 ]
adcx r11, r8
adcx r15, rax
mov r8, rbx
xor rax, rax
adox r8, [ rsp + 0x138 ]
adox rbp, [ rsp + 0x128 ]
adcx r8, [ rsp - 0x38 ]
adcx rbp, [ rsp - 0x40 ]
mov rdx, r9
mulx rbx, r9, [ rsi + 0x8 ]
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x150 ], r13
mov [ rsp + 0x158 ], rbx
mulx rbx, r13, rdx
mov rdx, rcx
add rdx, [ rsp + 0x120 ]
adcx r10, [ rsp + 0x118 ]
mov rcx, r11
shrd rcx, r15, 58
shr r15, 58
mov [ rsp + 0x160 ], r9
mov r9, rdx
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0x168 ], rbx
mov [ rsp + 0x170 ], r13
mulx r13, rbx, [ rsi + 0x10 ]
test al, al
adox r9, rcx
adox r15, r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x178 ], r13
mulx r13, rcx, r14
mov rdx, r9
shrd rdx, r15, 58
shr r15, 58
xor r14, r14
adox r8, rdx
adox r15, rbp
mov rbp, r8
shrd rbp, r15, 58
shr r15, 58
test al, al
adox rcx, [ rsp + 0x170 ]
adox r13, [ rsp + 0x168 ]
mov rdx, 0x3a 
bzhi r14, r8, rdx
bzhi r8, r9, rdx
adox rcx, rbx
adox r13, [ rsp + 0x178 ]
add rcx, [ rsp + 0x160 ]
adcx r13, [ rsp + 0x158 ]
xor rbx, rbx
adox rcx, [ rsp + 0xf0 ]
adox r13, [ rsp + 0xe8 ]
adcx rcx, rbp
adcx r15, r13
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x28 ], r14
mov rdx, [ rsi + 0x20 ]
mulx r14, rbp, rdx
test al, al
adox rbp, [ rsp + 0x78 ]
adox r14, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, rax
mov rdx, [ rsp + 0x18 ]
mulx r9, rax, [ rsi + 0x40 ]
xchg rdx, r10
mov [ rsp + 0x180 ], r8
mov [ rsp + 0x188 ], r15
mulx r15, r8, [ rsi + 0x18 ]
adcx rbp, [ rsp + 0x110 ]
adcx r14, [ rsp + 0x108 ]
xor rdx, rdx
adox rax, r8
adox r15, r9
adcx rax, r13
adcx rbx, r15
add rax, [ rsp + 0x100 ]
adcx rbx, [ rsp + 0xf8 ]
mov rdx, r12
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0x3a 
bzhi r9, rcx, rdx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x30 ], r9
mov r15, [ rsp + 0x188 ]
shrd rcx, r15, 58
shr r15, 58
add rax, r12
adcx r13, rbx
add rax, rcx
adcx r15, r13
mov rbx, rax
shrd rbx, r15, 58
shr r15, 58
bzhi r12, rdi, rdx
adox rbp, [ rsp + 0x30 ]
adox r14, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, rdi, r10
test al, al
adox rbp, rdi
adox r9, r14
adcx rbp, rbx
adcx r15, r9
mov rdx, 0x1ffffffffffffff 
mov r10, rbp
and r10, rdx
mov [ r8 + 0x40 ], r10
shrd rbp, r15, 57
shr r15, 57
xor rcx, rcx
adox rbp, [ rsp + 0xe0 ]
adox r15, rcx
mov r13, rbp
shrd r13, r15, 58
mov rbx, 0x3ffffffffffffff 
and rbp, rbx
mov [ r8 + 0x0 ], rbp
lea r13, [ r13 + r12 ]
mov r12, r13
and r12, rbx
and rax, rbx
shr r13, 58
mov [ r8 + 0x8 ], r12
mov [ r8 + 0x38 ], rax
add r13, [ rsp + 0x150 ]
and r11, rbx
mov r14, [ rsp + 0x180 ]
mov [ r8 + 0x20 ], r14
mov [ r8 + 0x10 ], r13
mov [ r8 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 528
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2509
; seed 4297053650544067 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2348127 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=181, initial num_batches=31): 99411 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04233629612026948
; number reverted permutation / tried permutation: 68830 / 90043 =76.441%
; number reverted decision / tried decision: 62595 / 89956 =69.584%
; validated in 1.474s
