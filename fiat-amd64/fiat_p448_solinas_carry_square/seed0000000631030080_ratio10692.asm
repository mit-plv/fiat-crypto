SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 448
mov rax, [ rsi + 0x30 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x28 ]
lea r11, [rax + rax]
mov rdx, [ rsi + 0x30 ]
mulx rcx, rax, rdx
mov rdx, 0x1 
shlx r8, [ rsi + 0x8 ], rdx
shlx r9, [ rsi + 0x38 ], rdx
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, r13
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r15
mulx r15, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rdi
mulx rdi, r14, r8
mov rdx, r10
mulx r8, r10, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, r12
mov rdx, r11
mov [ rsp - 0x8 ], r13
mulx r13, r11, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r8
mulx r8, r14, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r8
mov r8, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r14
lea r14, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], rbx
mulx rbx, r10, r12
mov rdx, r8
mov [ rsp + 0x30 ], r9
mulx r9, r8, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r9
mov r9, rax
mov [ rsp + 0x40 ], r8
xor r8, r8
adox r9, r10
mov [ rsp + 0x48 ], r13
mov r13, rbx
adox r13, rcx
mov [ rsp + 0x50 ], r11
mov r11, r9
adcx r11, rbp
mov [ rsp + 0x58 ], r14
mov r14, r15
adcx r14, r13
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r14
mov [ rsp + 0x68 ], r11
mulx r11, r14, [ rsp + 0x58 ]
xor rdx, rdx
adox r9, rax
adox rcx, r13
mov rax, [ rsp + 0x68 ]
adcx rax, [ rsp + 0x50 ]
mov r13, [ rsp + 0x60 ]
adcx r13, [ rsp + 0x48 ]
add r9, r10
adcx rbx, rcx
xor r10, r10
adox r9, rbp
adox r15, rbx
adcx r9, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x48 ]
mov rdx, [ rsp + 0x30 ]
mov rbp, rdx
xor rcx, rcx
adox rbp, rdx
mov r10, [ rsp + 0x28 ]
mov rbx, r10
adox rbx, r10
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r11
mov [ rsp + 0x78 ], r14
mulx r14, r11, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], r11
mulx r11, r14, r8
adcx rbp, r14
mov rdx, r11
adcx rdx, rbx
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], r13
mulx r13, rbx, rdi
xor rdx, rdx
adox rcx, r14
adox r11, r10
adcx rcx, rbx
mov r10, r13
adcx r10, r11
mov rdx, [ rsi + 0x38 ]
mulx r11, r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], r8
mulx r8, rax, rdx
test al, al
adox rcx, [ rsp - 0x10 ]
adox r10, [ rsp - 0x28 ]
mov rdx, r14
adcx rdx, rax
mov [ rsp + 0xa8 ], r10
mov r10, r8
adcx r10, r11
test al, al
adox rbp, rbx
adox r13, [ rsp + 0xa0 ]
mov rbx, [ rsp + 0x98 ]
adcx rbx, [ rsp + 0x20 ]
mov [ rsp + 0xb0 ], rcx
mov rcx, [ rsp + 0x90 ]
adcx rcx, [ rsp + 0x8 ]
mov [ rsp + 0xb8 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], r13
mov [ rsp + 0xc8 ], rbp
mulx rbp, r13, r12
test al, al
adox rbx, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
mov rdx, rdi
mov [ rsp + 0xd0 ], r10
mulx r10, rdi, [ rsi + 0x28 ]
adcx rdi, r13
adcx rbp, r10
mov r13, [ rsp - 0x10 ]
mov r10, r13
mov [ rsp + 0xd8 ], rcx
xor rcx, rcx
adox r10, [ rsp + 0xc8 ]
mov [ rsp + 0xe0 ], rbx
mov rbx, [ rsp - 0x28 ]
adox rbx, [ rsp + 0xc0 ]
mov r13, r14
adcx r13, r14
adcx r11, r11
mulx rcx, r14, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r10
mulx r10, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox r13, rax
adox r8, r11
mov rax, rdi
adcx rax, [ rsp + 0x78 ]
mov r11, rbp
adcx r11, [ rsp + 0x70 ]
add rax, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
add r13, r14
mov [ rsp + 0xf8 ], r11
mov r11, rcx
adcx r11, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r11
mulx r11, r8, rdx
xor rdx, rdx
adox rax, rbx
adox r10, [ rsp + 0xf8 ]
mov rdx, r12
mulx rbx, r12, [ rsi + 0x0 ]
adcx rax, r12
adcx rbx, r10
mov rdx, rax
shrd rdx, rbx, 56
mov r10, r8
xor r12, r12
adox r10, [ rsp + 0xe0 ]
adox r11, [ rsp + 0xd8 ]
mov r8, 0x38 
bzhi r12, rax, r8
mov rax, rdx
adox rax, r10
mov rbx, 0x0 
adox r11, rbx
mov r10, rax
shrd r10, r11, 56
mov r11, [ rsi + 0x10 ]
lea rbx, [r11 + r11]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], r12
mulx r12, r8, rdx
mov rdx, rbx
mov [ rsp + 0x110 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
mov [ rsp + 0x118 ], r12
mov [ rsp + 0x120 ], r8
mulx r8, r12, [ rsi + 0x0 ]
add rdi, rbx
adcx r13, rbp
mov rbp, r14
xor rdx, rdx
adox rbp, [ rsp + 0xd0 ]
adox rcx, [ rsp + 0xb8 ]
mov r14, [ rsp + 0xb0 ]
adcx r14, [ rsp - 0x18 ]
mov rbx, [ rsp + 0xa8 ]
adcx rbx, [ rsp - 0x20 ]
add r14, r10
adc rbx, 0x0
xor r10, r10
adox rbp, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov rdx, 0x38 
bzhi r10, r14, rdx
adox rbp, [ rsp + 0x120 ]
adox rcx, [ rsp + 0x118 ]
mov [ rsp + 0x128 ], r10
bzhi r10, rax, rdx
shrd r14, rbx, 56
imul rax, [ rsi + 0x18 ], 0x2
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r10
mulx r10, rbx, rax
mov rdx, rax
mov [ rsp + 0x138 ], r10
mulx r10, rax, [ rsi + 0x0 ]
add rdi, rax
adcx r10, r13
xor r13, r13
adox rbp, r12
adox r8, rcx
adcx rbp, r14
adc r8, 0x0
mov r12, 0x38 
bzhi rcx, rbp, r12
mulx rax, r14, [ rsi + 0x8 ]
bzhi rdx, rdi, r12
shrd rbp, r8, 56
lea rbp, [ rbp + rdx ]
xor r8, r8
adox r9, [ rsp + 0x20 ]
adox r15, [ rsp + 0x8 ]
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], rcx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rdx
adcx r9, rcx
adcx r8, r15
xor rdx, rdx
adox r9, [ rsp + 0x0 ]
adox r8, [ rsp - 0x8 ]
adcx r9, r14
adcx rax, r8
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rsp + 0x58 ]
xor rdx, rdx
adox r9, rcx
adox r8, rax
shrd rdi, r10, 56
add r9, rdi
adc r8, 0x0
mov r10, rbx
xor rax, rax
adox r10, [ rsp + 0xf0 ]
mov rdx, [ rsp + 0xe8 ]
adox rdx, [ rsp + 0x138 ]
mov rbx, rbp
shr rbx, 56
mov rcx, rdx
mov rdx, [ rsp + 0x58 ]
mulx rax, rdi, [ rsi + 0x8 ]
test al, al
adox r11, r9
mov r12, 0x0 
adox r8, r12
adcx r10, rdi
adcx rax, rcx
mov r9, [ rsp + 0x110 ]
xor rcx, rcx
adox r9, [ rsp - 0x40 ]
mov r12, [ rsp + 0x100 ]
adox r12, [ rsp - 0x48 ]
mulx rcx, rdi, [ rsi + 0x10 ]
mov rdx, r11
shrd rdx, r8, 56
xor r8, r8
adox r10, [ rsp + 0x18 ]
adox rax, [ rsp + 0x10 ]
adcx r10, rdx
adc rax, 0x0
add r9, r14
adcx r15, r12
mov r14, 0xffffffffffffff 
and r11, r14
adox r9, rdi
adox rcx, r15
adcx r9, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x38 ]
mov r12, r10
and r12, r14
shrd r10, rax, 56
xor rdi, rdi
adox r9, [ rsp + 0x88 ]
adox rcx, [ rsp + 0x80 ]
adcx r9, r10
adc rcx, 0x0
mov r8, r9
shrd r8, rcx, 56
add r8, [ rsp + 0x108 ]
mov rdx, r8
shr rdx, 56
and r8, r14
mov rax, rdx
add rax, [ rsp + 0x130 ]
mov r15, rax
and r15, r14
shr rax, 56
add rax, [ rsp + 0x128 ]
mov [ r13 + 0x8 ], rax
lea r11, [ r11 + rdx ]
lea rbx, [ rbx + r11 ]
mov r10, rbx
and r10, r14
mov [ r13 + 0x20 ], r10
shr rbx, 56
mov [ r13 + 0x0 ], r15
lea rbx, [ rbx + r12 ]
and rbp, r14
mov [ r13 + 0x18 ], rbp
and r9, r14
mov [ r13 + 0x38 ], r8
mov [ r13 + 0x30 ], r9
mov [ r13 + 0x28 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 448
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.0692
; seed 1500889305502349 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2446240 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=192, initial num_batches=31): 103463 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.042294705343711166
; number reverted permutation / tried permutation: 71423 / 89678 =79.644%
; number reverted decision / tried decision: 66380 / 90321 =73.493%
; validated in 1.306s
