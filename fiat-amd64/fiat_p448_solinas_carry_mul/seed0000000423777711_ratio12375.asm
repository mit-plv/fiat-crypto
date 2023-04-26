SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 568
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x30 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x38 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x38 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rsi + 0x38 ]
mov rdx, r14
mov [ rsp - 0x18 ], rdi
xor rdi, rdi
adox rdx, r10
mov [ rsp - 0x10 ], r15
mov r15, r11
adox r15, r13
mov rdi, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r12
mov [ rsp + 0x40 ], rbp
mulx rbp, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x58 ], r12
mov [ rsp + 0x60 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, r14
adcx rdx, r14
adcx r13, r13
mov r14, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
test al, al
adox r14, r10
adox r11, r13
mov rdx, [ rsi + 0x20 ]
mulx r13, r10, [ rax + 0x30 ]
adcx r14, r9
mov rdx, rbx
adcx rdx, r11
add rdi, r9
adcx rbx, r15
add r14, r12
mov r15, rbp
adcx r15, rdx
test al, al
adox r14, r10
mov r9, r13
adox r9, r15
adcx rdi, r12
adcx rbp, rbx
xor r12, r12
adox rdi, r10
adox r13, rbp
mov rdx, [ rax + 0x30 ]
mulx r10, r11, [ rsi + 0x30 ]
mov rdx, r8
adcx rdx, r11
mov rbx, r10
adcx rbx, rcx
mov r15, rdx
mov rdx, [ rax + 0x38 ]
mulx r12, rbp, [ rsi + 0x28 ]
add r15, rbp
mov rdx, r12
adcx rdx, rbx
mov rbx, r15
test al, al
adox rbx, [ rsp + 0x90 ]
mov [ rsp + 0x98 ], r13
mov r13, rdx
adox r13, [ rsp + 0x88 ]
adcx r15, r8
adcx rcx, rdx
add r15, r11
adcx r10, rcx
mov rdx, [ rsi + 0x18 ]
mulx r11, r8, [ rax + 0x38 ]
xor rdx, rdx
adox r15, rbp
adox r12, r10
adcx r15, [ rsp + 0x90 ]
adcx r12, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x30 ]
mulx rcx, rbp, [ rax + 0x38 ]
add r14, r8
mov rdx, r11
adcx rdx, r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa0 ], r14
mulx r14, r10, [ rax + 0x28 ]
add rdi, r8
adcx r11, [ rsp + 0x98 ]
xor rdx, rdx
adox rbx, [ rsp + 0x80 ]
adox r13, [ rsp + 0x78 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa8 ], r11
mulx r11, r8, [ rsi + 0x38 ]
adcx r8, r10
adcx r14, r11
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x38 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xb0 ], rdi
mov [ rsp + 0xb8 ], r13
mulx r13, rdi, [ rax + 0x30 ]
xor rdx, rdx
adox r15, [ rsp + 0x80 ]
adox r12, [ rsp + 0x78 ]
mov [ rsp + 0xc0 ], rbx
mov rbx, rdi
adcx rbx, rbp
mov [ rsp + 0xc8 ], r12
mov r12, rcx
adcx r12, r13
mov [ rsp + 0xd0 ], r15
mov r15, rbx
add r15, rdi
adcx r13, r12
add r8, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
add r8, r10
adcx r11, r14
mov rdx, [ rax + 0x18 ]
mulx rdi, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xd8 ], r11
mulx r11, r14, [ rsi + 0x38 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe0 ], r8
mov [ rsp + 0xe8 ], rdi
mulx rdi, r8, [ rsi + 0x30 ]
mov rdx, r8
test al, al
adox rdx, [ rsp + 0xa0 ]
adox rdi, r9
adcx r15, rbp
adcx rcx, r13
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, r9, [ rax + 0x20 ]
add r15, r14
mov rdx, r11
adcx rdx, rcx
add rbx, r14
adcx r11, r12
add r15, r10
adcx rdx, [ rsp + 0xe8 ]
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mulx r8, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], r8
mulx r8, rcx, [ rax + 0x28 ]
xor rdx, rdx
adox rbx, r10
adox r11, [ rsp + 0xe8 ]
adcx rbx, r9
mov r10, r13
adcx r10, r11
add rbx, rcx
mov r11, r8
adcx r11, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r14
mulx r14, r10, [ rax + 0x18 ]
mov rdx, r10
test al, al
adox rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x100 ], r12
mov r12, r14
adox r12, [ rsp + 0xc8 ]
mov [ rsp + 0x108 ], r12
mov r12, r10
adcx r12, [ rsp + 0xc0 ]
adcx r14, [ rsp + 0xb8 ]
add rbp, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x18 ]
mov r10, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], rbp
mulx rbp, rdi, [ rsi + 0x38 ]
test al, al
adox rbx, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
adcx r15, r9
adcx r13, [ rsp + 0x100 ]
mov rdx, rdi
add rdx, [ rsp + 0xe0 ]
adcx rbp, [ rsp + 0xd8 ]
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x120 ], r10
mulx r10, rdi, [ rsi + 0x30 ]
add r15, rcx
adcx r8, r13
add rbx, [ rsp - 0x20 ]
adcx r11, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, rcx, [ rax + 0x20 ]
test al, al
adox r9, rdi
adox r10, rbp
mov rdx, [ rsi + 0x20 ]
mulx rdi, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], r15
mulx r15, r8, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x138 ], r11
mov [ rsp + 0x140 ], rbx
mulx rbx, r11, [ rax + 0x38 ]
adcx r9, [ rsp + 0xf8 ]
adcx r10, [ rsp + 0xf0 ]
test al, al
adox r9, rbp
adox rdi, r10
mov rdx, [ rax + 0x20 ]
mulx r10, rbp, [ rsi + 0x18 ]
adcx r12, rcx
mov rdx, r13
adcx rdx, r14
test al, al
adox r9, rbp
adox r10, rdi
adcx r9, r8
adcx r15, r10
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mulx rdi, r8, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r8
adox rdi, r15
adcx r9, r11
adcx rbx, rdi
mov r11, rcx
xor rbp, rbp
adox r11, [ rsp + 0x120 ]
adox r13, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, [ rax + 0x28 ]
adcx r11, rcx
mov rdx, r10
adcx rdx, r13
mov r15, r9
shrd r15, rbx, 56
xor r8, r8
adox r12, rcx
adox r10, r14
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ rax + 0x0 ]
adcx r11, [ rsp + 0x70 ]
adcx rbp, [ rsp + 0x68 ]
mov rdx, 0x38 
bzhi r13, r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], rbx
mulx rbx, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x158 ], r9
mov [ rsp + 0x160 ], r15
mulx r15, r9, [ rax + 0x0 ]
mov rdx, r9
adox rdx, [ rsp + 0xe0 ]
adox r15, [ rsp + 0xd8 ]
test al, al
adox r12, [ rsp + 0x70 ]
adox r10, [ rsp + 0x68 ]
adcx rdx, rcx
adcx r8, r15
xor rcx, rcx
adox r12, r13
mov r9, rbx
adox r9, r10
mov r15, r14
adcx r15, [ rsp + 0x140 ]
adcx rdi, [ rsp + 0x138 ]
test al, al
adox r15, [ rsp + 0x50 ]
adox rdi, [ rsp + 0x48 ]
adcx r12, [ rsp + 0x10 ]
adcx r9, [ rsp + 0x8 ]
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rax + 0x10 ]
add r14, r10
adcx rcx, r8
test al, al
adox r11, r13
adox rbx, rbp
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x168 ], r13
mov [ rsp + 0x170 ], rbp
mulx rbp, r13, [ rax + 0x0 ]
mov rdx, r12
adcx rdx, [ rsp + 0x160 ]
adc r9, 0x0
xor r12, r12
adox r14, r8
adox r10, rcx
mov rcx, rdx
shrd rcx, r9, 56
test al, al
adox r15, rcx
adox rdi, r12
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffff 
and r8, rdx
adox r11, r13
adox rbp, rbx
adcx r11, r9
adcx rcx, rbp
xor rbx, rbx
adox r11, [ rsp + 0x30 ]
adox rcx, [ rsp + 0x28 ]
mov r12, [ rsp + 0x118 ]
adcx r12, [ rsp + 0x60 ]
mov r13, [ rsp + 0x110 ]
adcx r13, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, [ rax + 0x18 ]
xor rdx, rdx
adox r12, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x178 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x170 ]
mov [ rsp + 0x180 ], r13
mov r13, rdx
adcx r13, [ rsp + 0xb0 ]
mov [ rsp + 0x188 ], r12
mov r12, [ rsp + 0x168 ]
adcx r12, [ rsp + 0xa8 ]
add r11, r9
adcx rbp, rcx
xor rdx, rdx
adox r11, [ rsp - 0x40 ]
adox rbp, [ rsp - 0x48 ]
mov rdx, [ rax + 0x10 ]
mulx r9, rcx, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x40 ]
mov [ rsp + 0x190 ], r9
mov r9, rdx
adcx r9, [ rsp + 0x130 ]
mov [ rsp + 0x198 ], rcx
mov rcx, [ rsp + 0x38 ]
adcx rcx, [ rsp + 0x128 ]
add r9, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a0 ], rcx
mov [ rsp + 0x1a8 ], r9
mulx r9, rcx, [ rax + 0x8 ]
xor rdx, rdx
adox r13, rcx
adox r9, r12
adcx r13, rbx
adcx r8, r9
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, [ rax + 0x20 ]
mov rdx, r15
shrd rdx, rdi, 56
add r13, rdx
adc r8, 0x0
mov rdi, r14
shrd rdi, r10, 56
mov r10, r13
shrd r10, r8, 56
xor rcx, rcx
adox r11, rdi
adox rbp, rcx
mov rdx, [ rax + 0x18 ]
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, rdi, [ rax + 0x0 ]
mov rdx, rdi
adcx rdx, [ rsp + 0x1a8 ]
adcx rcx, [ rsp + 0x1a0 ]
mov rdi, r11
add rdi, [ rsp + 0x160 ]
adc rbp, 0x0
xor r11, r11
adox rdx, [ rsp + 0x158 ]
adox rcx, [ rsp + 0x150 ]
mov r11, 0xffffffffffffff 
and r14, r11
adox rdx, [ rsp + 0x198 ]
adox rcx, [ rsp + 0x190 ]
adcx rdx, r9
adcx r8, rcx
xor r9, r9
adox rdx, rbx
adox r12, r8
lea r10, [ r10 + r14 ]
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r14, [ rax + 0x30 ]
mov rdx, r10
and rdx, r11
and r13, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], rdx
mov rdx, [ rax + 0x28 ]
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1b0 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, r8
adox rdx, [ rsp + 0x188 ]
adox rcx, [ rsp + 0x180 ]
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r13
mov r13, 0x38 
bzhi r8, rdi, r13
adox rbx, [ rsp + 0x20 ]
adox r12, [ rsp + 0x18 ]
shrd rdi, rbp, 56
test al, al
adox rbx, rdi
mov rbp, 0x0 
adox r12, rbp
adcx rdx, r9
adcx r11, rcx
bzhi r9, rbx, r13
shrd rbx, r12, 56
xor rcx, rcx
adox rdx, r14
adox r11, [ rsp + 0x1b0 ]
adcx rdx, rbx
adc r11, 0x0
mov rbp, rdx
shrd rbp, r11, 56
add rbp, [ rsp + 0x148 ]
mov r14, rbp
shr r14, 56
lea r8, [ r8 + r14 ]
shr r10, 56
lea r10, [ r10 + r8 ]
bzhi rdi, r10, r13
add r14, [ rsp + 0x178 ]
mov r12, r14
shr r12, 56
bzhi rbx, r14, r13
bzhi r11, r15, r13
shr r10, 56
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], rbx
lea r12, [ r12 + r11 ]
bzhi r8, rbp, r13
bzhi rbp, rdx, r13
mov [ r15 + 0x38 ], r8
mov [ r15 + 0x30 ], rbp
lea r10, [ r10 + r9 ]
mov [ r15 + 0x20 ], rdi
mov [ r15 + 0x8 ], r12
mov [ r15 + 0x28 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 568
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2375
; seed 0317353833864785 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8535234 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=109, initial num_batches=31): 213866 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02505684085521264
; number reverted permutation / tried permutation: 63885 / 89988 =70.993%
; number reverted decision / tried decision: 50913 / 90011 =56.563%
; validated in 6.431s
