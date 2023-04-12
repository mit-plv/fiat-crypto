SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 440
mov rax, 0x1 
shlx r10, [ rsi + 0x28 ], rax
mov rdx, [ rsi + 0x38 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x38 ]
lea r8, [rdx + rdx]
mov rdx, r10
mulx r9, r10, [ rsi + 0x20 ]
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, r8
mov [ rsp - 0x70 ], r12
mulx r12, r8, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
imul r13, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov rdi, 0x1 
mov [ rsp - 0x48 ], r15
shlx r15, [ rsi + 0x18 ], rdi
mov [ rsp - 0x40 ], r14
mulx r14, rdi, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r15
mov r15, rdi
mov [ rsp - 0x30 ], r13
xor r13, r13
adox r15, r10
mov [ rsp - 0x28 ], rbp
mov rbp, r9
adox rbp, r14
mov [ rsp - 0x20 ], rbp
mulx rbp, r13, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], rbp
mulx rbp, r15, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r13
mov r13, rdi
adcx r13, rdi
adcx r14, r14
mov rdi, 0x1 
mov [ rsp + 0x0 ], rbx
shlx rbx, [ rsi + 0x30 ], rdi
xchg rdx, rbx
mov [ rsp + 0x8 ], rbp
mulx rbp, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r15
mulx r15, rbp, [ rsi + 0x10 ]
test al, al
adox r13, r10
adox r9, r14
mulx r14, r10, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r14
mov r14, r11
adcx r14, r11
mov [ rsp + 0x38 ], r10
mov r10, rcx
adcx r10, rcx
mov [ rsp + 0x40 ], r10
xor r10, r10
adox rdi, r8
adox r12, [ rsp + 0x18 ]
adcx r13, [ rsp + 0x28 ]
adcx r9, [ rsp + 0x20 ]
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], r9
mulx r9, r10, rdx
mov rdx, r8
mov [ rsp + 0x50 ], r13
mulx r13, r8, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], rdi
mulx rdi, r12, rax
mov rdx, r10
mov [ rsp + 0x70 ], r15
xor r15, r15
adox rdx, [ rsp + 0x10 ]
mov [ rsp + 0x78 ], rbp
mov rbp, r9
adox rbp, [ rsp + 0x8 ]
mov [ rsp + 0x80 ], rdi
mov rdi, rdx
adcx rdi, r10
adcx r9, rbp
xor r10, r10
adox rdi, [ rsp + 0x10 ]
adox r9, [ rsp + 0x8 ]
adcx r11, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x28 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r9
mulx r9, r10, rdx
add r11, r8
mov rdx, r13
adcx rdx, rcx
imul rcx, [ rsi + 0x20 ], 0x2
mov [ rsp + 0x90 ], rdx
xor rdx, rdx
adox r15, r10
mov [ rsp + 0x98 ], r11
mov r11, r9
adox r11, rbp
adcx r15, r12
adcx r11, [ rsp + 0x80 ]
mov rdx, rax
mulx rbp, rax, [ rsi + 0x10 ]
add rdi, r10
adcx r9, [ rsp + 0x88 ]
xchg rdx, rcx
mov [ rsp + 0xa0 ], r9
mulx r9, r10, [ rsi + 0x18 ]
add r15, [ rsp + 0x78 ]
adcx r11, [ rsp + 0x70 ]
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], r15
mulx r15, r11, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r15
mov r15, r10
mov [ rsp + 0xc0 ], r11
xor r11, r11
adox r15, [ rsp + 0x68 ]
adox r9, [ rsp + 0x60 ]
mulx r11, r10, [ rsi + 0x10 ]
adcx r15, rax
adcx rbp, r9
mulx r9, rax, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, r12
mov [ rsp + 0xc8 ], r11
mov r11, [ rsp + 0x80 ]
adox r11, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x78 ]
adcx r11, [ rsp + 0x70 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r10
mulx r10, r12, r14
xor rdx, rdx
adox r15, r12
adox r10, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r14, [ rsp - 0x30 ]
mov rdx, r14
adcx rdx, [ rsp + 0x68 ]
adcx rbp, [ rsp + 0x60 ]
mov r12, rdx
mov rdx, [ rsp - 0x38 ]
mov [ rsp + 0xd8 ], r9
mulx r9, r14, [ rsi + 0x0 ]
test al, al
adox r12, r14
adox r9, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], rax
mulx rax, r14, rdx
mov rdx, [ rsp + 0x58 ]
adcx rdx, [ rsp + 0x0 ]
mov [ rsp + 0xe8 ], r10
mov r10, [ rsp + 0x40 ]
adcx r10, [ rsp - 0x28 ]
mov [ rsp + 0xf0 ], r10
mov r10, r12
shrd r10, r9, 56
add rdi, r14
adcx rax, r11
mov r11, [ rsp + 0x50 ]
add r11, [ rsp - 0x8 ]
mov r9, [ rsp + 0x48 ]
adcx r9, [ rsp - 0x10 ]
mov r14, 0x38 
mov [ rsp + 0xf8 ], rdx
bzhi rdx, r12, r14
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r9
mulx r9, r14, rbx
adox r15, r14
adox r9, [ rsp + 0xe8 ]
mov rdx, rbx
mulx r14, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox rdi, [ rsp - 0x40 ]
adox rax, [ rsp - 0x48 ]
mov rdx, rbp
mov [ rsp + 0x108 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
adcx rdi, rbp
adcx r12, rax
mulx rbp, rax, [ rsi + 0x10 ]
add rdi, [ rsp + 0xe0 ]
adcx r12, [ rsp + 0xd8 ]
xor rdx, rdx
adox rdi, r10
adox r12, rdx
mov r10, r15
shrd r10, r9, 56
mov r9, r10
test al, al
adox r9, rdi
adox r12, rdx
mov rdi, r9
shrd rdi, r12, 56
xor r12, r12
adox r11, rax
adox rbp, [ rsp + 0x100 ]
adcx r11, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0xb8 ]
mov rdx, rbx
xor rax, rax
adox rdx, [ rsp + 0x98 ]
mov r12, r14
adox r12, [ rsp + 0x90 ]
mov [ rsp + 0x110 ], r12
mov r12, r8
adcx r12, [ rsp + 0xf8 ]
adcx r13, [ rsp + 0xf0 ]
mov r8, [ rsp - 0x18 ]
test al, al
adox r8, [ rsp + 0x28 ]
mov [ rsp + 0x118 ], rdx
mov rdx, [ rsp - 0x20 ]
adox rdx, [ rsp + 0x20 ]
adcx r12, rbx
adcx r14, r13
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r13, rdx
test al, al
adox r12, r13
adox rax, r14
mov rdx, rcx
mulx r14, rcx, [ rsi + 0x0 ]
adcx r11, rcx
adcx r14, rbp
mulx r13, rbp, [ rsi + 0x8 ]
add r8, [ rsp - 0x8 ]
adcx rbx, [ rsp - 0x10 ]
imul rdx, [ rsi + 0x8 ], 0x2
mov rcx, [ rsp + 0xb0 ]
add rcx, [ rsp - 0x40 ]
mov [ rsp + 0x120 ], r13
mov r13, [ rsp + 0xa8 ]
adcx r13, [ rsp - 0x48 ]
mov [ rsp + 0x128 ], rbp
mov [ rsp + 0x130 ], rax
mulx rax, rbp, [ rsi + 0x0 ]
test al, al
adox r8, rbp
adox rax, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbp, rbx, rdx
adcx rcx, rbx
adcx rbp, r13
add r10, rcx
adc rbp, 0x0
mov rdx, r10
shrd rdx, rbp, 56
add r11, rdi
adc r14, 0x0
add r8, rdx
adc rax, 0x0
add r12, [ rsp + 0xd0 ]
mov rdi, [ rsp + 0xc8 ]
adcx rdi, [ rsp + 0x130 ]
add r12, [ rsp + 0x128 ]
adcx rdi, [ rsp + 0x120 ]
xor r13, r13
adox r12, [ rsp + 0x38 ]
adox rdi, [ rsp + 0x30 ]
mov rbx, 0x38 
bzhi rcx, r11, rbx
shrd r11, r14, 56
mov rbp, r8
shrd rbp, rax, 56
add r12, r11
adc rdi, 0x0
bzhi rdx, r15, rbx
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx rax, r14, rdx
mov rdx, r12
shrd rdx, rdi, 56
lea rdx, [ rdx + r15 ]
bzhi r11, rdx, rbx
shr rdx, 56
mov rdi, rdx
mov rdx, [ rsp - 0x30 ]
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, r14
xor rbx, rbx
adox rdx, [ rsp + 0x118 ]
adox rax, [ rsp + 0x110 ]
mov r14, 0xffffffffffffff 
and r10, r14
adox rdx, r15
adox r13, rax
adcx rdx, rbp
adc r13, 0x0
mov rbp, rdx
and rbp, r14
lea r10, [ r10 + rdi ]
mov r15, r10
and r15, r14
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x10 ], rbp
and r8, r14
shrd rdx, r13, 56
shr r10, 56
mov [ rax + 0x0 ], r15
and r9, r14
lea r9, [ r9 + rdi ]
add rdx, [ rsp + 0x108 ]
mov rdi, rdx
shr rdi, 56
lea rdi, [ rdi + r9 ]
mov r13, rdi
and r13, r14
lea r10, [ r10 + r8 ]
mov [ rax + 0x20 ], r13
shr rdi, 56
mov [ rax + 0x8 ], r10
and r12, r14
and rdx, r14
mov [ rax + 0x18 ], rdx
mov [ rax + 0x38 ], r11
mov [ rax + 0x30 ], r12
lea rdi, [ rdi + rcx ]
mov [ rax + 0x28 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 440
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1280
; seed 0461231243093551 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2424022 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=192, initial num_batches=31): 102746 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04238657899969555
; number reverted permutation / tried permutation: 73308 / 89951 =81.498%
; number reverted decision / tried decision: 66581 / 90048 =73.939%
; validated in 1.133s
