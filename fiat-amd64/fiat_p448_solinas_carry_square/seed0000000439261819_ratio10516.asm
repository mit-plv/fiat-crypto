SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 424
mov rax, [ rsi + 0x28 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x30 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
mov rdx, r12
mov [ rsp - 0x58 ], r15
mulx r15, r12, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov rdi, 0x1 
mov [ rsp - 0x48 ], rbx
shlx rbx, [ rsi + 0x18 ], rdi
mov rdi, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbx
lea rbx, [rdi + rdi]
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], rbp
mulx rbp, r9, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rbp
lea rbp, [rdx + rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r14
mulx r14, r9, rbp
mov rdx, rax
mov [ rsp - 0x8 ], r14
xor r14, r14
adox rdx, r12
mov [ rsp + 0x0 ], r9
mov r9, r15
adox r9, r11
mov [ rsp + 0x8 ], r13
mov r13, rdx
adcx r13, rax
adcx r11, r9
xchg rdx, rbp
mulx r14, rax, [ rsi + 0x20 ]
add rbp, rcx
mov [ rsp + 0x10 ], r14
mov r14, r8
adcx r14, r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x18 ], rax
mov [ rsp + 0x20 ], r14
mulx r14, rax, rdi
xor rdx, rdx
adox r13, r12
adox r15, r11
mov r12, rax
adcx r12, rax
mov r11, r14
adcx r11, r14
mov rdx, r10
mov [ rsp + 0x28 ], r11
mulx r11, r10, [ rsi + 0x18 ]
test al, al
adox r13, rcx
adox r8, r15
xchg rdx, rdi
mulx r15, rcx, [ rsi + 0x10 ]
xchg rdx, r9
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rcx
mulx rcx, r15, [ rsi + 0x0 ]
adcx rbp, r10
mov [ rsp + 0x40 ], rcx
mov rcx, r11
adcx rcx, [ rsp + 0x20 ]
test al, al
adox r13, r10
adox r11, r8
mulx r8, r10, [ rsi + 0x10 ]
adcx rbp, r10
mov [ rsp + 0x48 ], r15
mov r15, r8
adcx r15, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], rbp
mulx rbp, r15, rdx
mov rdx, [ rsp + 0x8 ]
mov [ rsp + 0x60 ], r12
mov r12, rdx
mov [ rsp + 0x68 ], rbp
xor rbp, rbp
adox r12, [ rsp + 0x0 ]
mov [ rsp + 0x70 ], r15
mov r15, [ rsp - 0x10 ]
adox r15, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x78 ], r15
mulx r15, rbp, r9
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x80 ], r15
mov [ rsp + 0x88 ], rbp
mulx rbp, r15, rdx
adcx r13, r10
adcx r8, r11
mov rdx, [ rsi + 0x18 ]
mulx r10, r11, [ rsp - 0x30 ]
add r13, [ rsp + 0x70 ]
adcx r8, [ rsp + 0x68 ]
mov rdx, rcx
mov [ rsp + 0x90 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r13
mov r13, r12
test al, al
adox r13, r11
adox r10, [ rsp + 0x78 ]
xchg rdx, rdi
mov [ rsp + 0xa0 ], r8
mulx r8, r11, [ rsi + 0x10 ]
adcx r13, r11
adcx r8, r10
mov r10, r15
add r10, r15
mov r11, rbp
adcx r11, rbp
test al, al
adox r10, [ rsp - 0x38 ]
adox r11, [ rsp - 0x48 ]
adcx r10, [ rsp + 0x18 ]
adcx r11, [ rsp + 0x10 ]
test al, al
adox r15, [ rsp - 0x38 ]
adox rbp, [ rsp - 0x48 ]
xchg rdx, r9
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], r10
mulx r10, r11, [ rsi + 0x0 ]
adcx r13, rcx
adcx r8, [ rsp + 0xa0 ]
xor rcx, rcx
adox r13, r11
adox r10, r8
mulx r8, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r10
mulx r10, rcx, rbx
adcx r15, [ rsp + 0x18 ]
adcx rbp, [ rsp + 0x10 ]
mov rdx, r11
add rdx, [ rsp + 0xb0 ]
mov rbx, r8
adcx rbx, [ rsp + 0xa8 ]
mov [ rsp + 0xc0 ], rbx
xor rbx, rbx
adox r15, r11
adox r8, rbp
mov r11, rdx
mov rdx, [ rsp - 0x40 ]
mulx rbx, rbp, [ rsi + 0x0 ]
adcx r12, rcx
adcx r10, [ rsp + 0x78 ]
xor rcx, rcx
adox r12, rbp
adox rbx, r10
mulx r10, rbp, [ rsi + 0x8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], r13
mulx r13, r11, rdx
adcx r15, r11
adcx r13, r8
mov rdx, [ rsp + 0x98 ]
test al, al
adox rdx, [ rsp + 0x88 ]
mov r8, [ rsp + 0x90 ]
adox r8, [ rsp + 0x80 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], r12
mulx r12, rbx, r9
adcx rax, rbx
mov rdx, r12
adcx rdx, r14
xor r14, r14
adox r11, rbp
adox r10, r8
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, [ rsp - 0x30 ]
adcx r11, r8
adcx r14, r10
mov rdx, [ rsi + 0x18 ]
mulx r8, r10, rdi
xor rdx, rdx
adox r15, [ rsp - 0x18 ]
adox r13, [ rsp - 0x28 ]
adcx rax, r10
mov rdi, r8
adcx rdi, rbp
mov rbp, [ rsp + 0xe0 ]
mov rdx, [ rsp + 0xd8 ]
mov [ rsp + 0xe8 ], r13
mov r13, rbp
shrd r13, rdx, 56
mov rdx, rbx
mov [ rsp + 0xf0 ], r15
xor r15, r15
adox rdx, [ rsp + 0x60 ]
adox r12, [ rsp + 0x28 ]
adcx rdx, r10
adcx r8, r12
test al, al
adox rax, [ rsp + 0x38 ]
adox rdi, [ rsp + 0x30 ]
adcx r11, r13
adc r14, 0x0
mov rbx, [ rsp + 0x58 ]
test al, al
adox rbx, [ rsp + 0x88 ]
mov r10, [ rsp + 0x50 ]
adox r10, [ rsp + 0x80 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], rdi
mulx rdi, rcx, rdx
adcx r13, [ rsp + 0x38 ]
adcx r8, [ rsp + 0x30 ]
xor rdx, rdx
adox r13, r12
adox r15, r8
adcx rbx, rcx
adcx rdi, r10
mov rdx, [ rsi + 0x8 ]
mulx r12, r10, r9
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x100 ], rax
mov [ rsp + 0x108 ], r12
mulx r12, rax, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x110 ], r10
mov [ rsp + 0x118 ], r12
mulx r12, r10, rdx
test al, al
adox r13, rcx
adox r8, r15
mov rdx, [ rsp + 0xd0 ]
mov r15, [ rsp + 0xb8 ]
mov rcx, rdx
shrd rcx, r15, 56
mov r15, rcx
test al, al
adox r15, rbx
mov [ rsp + 0x120 ], r8
mov r8, 0x0 
adox rdi, r8
adcx rcx, r11
adc r14, 0x0
mov r11, r10
xor rbx, rbx
adox r11, [ rsp + 0xc8 ]
adox r12, [ rsp + 0xc0 ]
mov r8, rcx
shrd r8, r14, 56
add r11, rax
adcx r12, [ rsp + 0x118 ]
xchg rdx, r9
mulx r10, rax, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, [ rsp + 0x110 ]
adox r12, [ rsp + 0x108 ]
adcx r13, rax
adcx r10, [ rsp + 0x120 ]
xor rbx, rbx
adox r13, r8
adox r10, rbx
mov rdx, 0x38 
bzhi r8, rcx, rdx
mov rcx, r13
shrd rcx, r10, 56
xor r14, r14
adox r11, [ rsp + 0x48 ]
adox r12, [ rsp + 0x40 ]
adcx r11, rcx
adc r12, 0x0
mov rbx, r11
shrd rbx, r12, 56
mov rdx, [ rsp - 0x20 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, rax
add rdx, [ rsp + 0x100 ]
adcx r10, [ rsp + 0xf8 ]
mov rcx, 0xffffffffffffff 
and r9, rcx
lea rbx, [ rbx + r9 ]
and r11, rcx
mov r12, r15
shrd r12, rdi, 56
xor rdi, rdi
adox rdx, r12
adox r10, rdi
mov r14, rbx
and r14, rcx
shr rbx, 56
lea r8, [ r8 + rbx ]
and r15, rcx
mov rax, rdx
shrd rax, r10, 56
mov r9, rax
xor r12, r12
adox r9, [ rsp + 0xf0 ]
mov rdi, [ rsp + 0xe8 ]
adox rdi, r12
lea r15, [ r15 + rbx ]
mov r10, r15
shr r10, 56
mov rbx, r9
shrd rbx, rdi, 56
and rbp, rcx
lea rbx, [ rbx + rbp ]
mov rax, rbx
shr rax, 56
lea rax, [ rax + r8 ]
mov r8, rax
and r8, rcx
shr rax, 56
and rbx, rcx
and r13, rcx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], rbx
mov [ rdi + 0x20 ], r8
and rdx, rcx
lea r10, [ r10 + rdx ]
lea rax, [ rax + r13 ]
mov [ rdi + 0x28 ], rax
and r15, rcx
and r9, rcx
mov [ rdi + 0x0 ], r15
mov [ rdi + 0x38 ], r14
mov [ rdi + 0x30 ], r11
mov [ rdi + 0x10 ], r9
mov [ rdi + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 424
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0516
; seed 4503457998365974 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2595512 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=119, initial num_batches=31): 89060 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03431307580161448
; number reverted permutation / tried permutation: 63219 / 90056 =70.200%
; number reverted decision / tried decision: 54003 / 89943 =60.041%
; validated in 1.143s
