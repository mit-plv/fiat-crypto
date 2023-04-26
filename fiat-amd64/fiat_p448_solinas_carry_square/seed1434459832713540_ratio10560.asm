SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 480
mov rax, [ rsi + 0x20 ]
mov r10, rax
shl r10, 0x1
mov rax, [ rsi + 0x38 ]
mov r11, rax
shl r11, 0x1
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, r11
mov rdx, 0x1 
shlx r8, [ rsi + 0x30 ], rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r10
mov rdx, r8
mov [ rsp - 0x60 ], r14
mulx r14, r8, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, rdx
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], rcx
mulx rcx, r12, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r12
mulx r12, rcx, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r8
mulx r8, r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r14
mulx r14, r8, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r8
mulx r8, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], r14
mulx r14, r8, rbp
imul rdx, [ rsi + 0x18 ], 0x2
mov [ rsp + 0x28 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r8
mov [ rsp + 0x38 ], r12
mulx r12, r8, r10
mov rdx, r10
mov [ rsp + 0x40 ], r14
mulx r14, r10, [ rsi + 0x8 ]
xchg rdx, rax
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r10
mulx r10, r14, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], r10
mov r10, r9
add r10, r9
mov [ rsp + 0x60 ], r14
mov r14, rbx
adcx r14, rbx
add r10, rdi
mov [ rsp + 0x68 ], r12
mov r12, r13
adcx r12, r14
xchg rdx, r15
mov [ rsp + 0x70 ], r8
mulx r8, r14, [ rsi + 0x18 ]
xchg rdx, r11
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r14
mulx r14, r8, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r14
xor r14, r14
adox r10, rcx
adox r12, [ rsp + 0x38 ]
xchg rdx, r15
mov [ rsp + 0x90 ], r8
mulx r8, r14, [ rsi + 0x18 ]
adcx r9, rdi
adcx r13, rbx
add r9, rcx
adcx r13, [ rsp + 0x38 ]
mov rbx, 0x1 
shlx rdi, [ rsi + 0x8 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, rbp
mov [ rsp + 0x98 ], r8
mulx r8, rbp, [ rsi + 0x0 ]
mov rdx, rax
mov [ rsp + 0xa0 ], r8
mulx r8, rax, [ rsi + 0x10 ]
mov rdx, r15
mov [ rsp + 0xa8 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r14
mov [ rsp + 0xb8 ], r13
mulx r13, r14, [ rsi + 0x30 ]
test al, al
adox r10, r15
mov [ rsp + 0xc0 ], r9
mov r9, rbp
adox r9, r12
adcx r10, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
test al, al
adox r10, rax
adox r8, r9
mov r12, r14
adcx r12, r14
mov rax, r13
adcx rax, r13
xor r9, r9
adox r10, rcx
adox rbx, r8
mulx r8, rcx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rax
mov rax, rcx
adcx rax, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
xor rcx, rcx
adox r14, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
adcx r14, [ rsp + 0x80 ]
adcx r13, [ rsp + 0x78 ]
xchg rdx, r11
mulx rcx, r9, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r12
mov [ rsp + 0xd8 ], r8
mulx r8, r12, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], r8
xor r8, r8
adox r14, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
adcx r10, r9
adcx rcx, rbx
xchg rdx, rdi
mulx r9, rbx, [ rsi + 0x0 ]
test al, al
adox r14, rbx
adox r9, r13
mov rdx, [ rsi + 0x0 ]
mulx rbx, r13, r11
mov rdx, rax
adcx rdx, [ rsp + 0x70 ]
mov [ rsp + 0xe8 ], rcx
mov rcx, [ rsp + 0x68 ]
adcx rcx, [ rsp + 0xd8 ]
mov [ rsp + 0xf0 ], r10
mov r10, r15
test al, al
adox r10, [ rsp + 0xc0 ]
adox rbp, [ rsp + 0xb8 ]
adcx rdx, [ rsp + 0x10 ]
adcx rcx, [ rsp + 0x8 ]
test al, al
adox rdx, r12
adox rcx, [ rsp + 0xe0 ]
adcx rdx, r13
adcx rbx, rcx
mov r15, rdx
shrd r15, rbx, 56
test al, al
adox r10, [ rsp + 0x20 ]
adox rbp, [ rsp + 0x18 ]
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mulx rcx, r13, rdx
mov rdx, r13
adcx rdx, [ rsp + 0x90 ]
mov rbx, rcx
adcx rbx, [ rsp + 0x88 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], rbp
mov [ rsp + 0x100 ], r10
mulx r10, rbp, rdx
mov rdx, r8
add rdx, r13
adcx rcx, rbx
xor r13, r13
adox rax, [ rsp + 0x30 ]
mov [ rsp + 0x108 ], r9
mov r9, [ rsp + 0x28 ]
adox r9, [ rsp + 0xd8 ]
adcx rdx, [ rsp + 0x90 ]
adcx rcx, [ rsp + 0x88 ]
mov r13, 0xffffffffffffff 
and r12, r13
mov r13, rdx
mov rdx, [ rsp + 0x40 ]
mov [ rsp + 0x110 ], r12
mov [ rsp + 0x118 ], r14
mulx r14, r12, [ rsi + 0x0 ]
adox rax, r12
adox r14, r9
mov r9, [ rsp + 0xd0 ]
adcx r9, [ rsp - 0x20 ]
mov r12, [ rsp + 0xc8 ]
adcx r12, [ rsp - 0x28 ]
add r8, rbp
mov [ rsp + 0x120 ], r15
mov r15, r10
adcx r15, rbx
mov rbx, 0xffffffffffffff 
mov [ rsp + 0x128 ], r15
mov r15, rax
and r15, rbx
adox r9, [ rsp + 0x80 ]
adox r12, [ rsp + 0x78 ]
adcx r9, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
add r13, rbp
adcx r10, rcx
mulx rcx, rbp, [ rsi + 0x10 ]
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r15
mov [ rsp + 0x138 ], r10
mulx r10, r15, rdi
xor rdx, rdx
adox r9, rbp
adox rcx, r12
adcx r8, [ rsp + 0xb0 ]
mov rdi, [ rsp + 0x98 ]
mov r12, rdi
adcx r12, [ rsp + 0x128 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], r13
mulx r13, rbp, r11
xor rdx, rdx
adox r8, r15
mov r11, r10
adox r11, r12
adcx r9, [ rsp + 0x50 ]
adcx rcx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x148 ], rcx
mulx rcx, r12, rdx
test al, al
adox r8, rbp
mov rdx, r13
adox rdx, r11
adcx r9, [ rsp + 0x60 ]
mov r11, [ rsp + 0x148 ]
adcx r11, [ rsp + 0x58 ]
add r8, r12
adcx rcx, rdx
mov r12, r8
xor rdx, rdx
adox r12, [ rsp + 0x120 ]
adox rcx, rdx
mov r8, [ rsp + 0x140 ]
adcx r8, [ rsp + 0xb0 ]
adcx rdi, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x150 ], r11
mov [ rsp + 0x158 ], r9
mulx r9, r11, rdx
add r8, r15
adcx r10, rdi
test al, al
adox r8, r11
adox r9, r10
mov rdx, 0xffffffffffffff 
mov r15, r12
and r15, rdx
adox r8, rbp
adox r13, r9
shrd r12, rcx, 56
mov rbp, r12
test al, al
adox rbp, [ rsp + 0x118 ]
mov rcx, [ rsp + 0x108 ]
mov rdi, 0x0 
adox rcx, rdi
mov rdx, [ rsi + 0x8 ]
mulx r10, r11, rbx
adcx r8, r11
adcx r10, r13
add r8, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
mov rdx, 0xffffffffffffff 
mov rbx, rbp
and rbx, rdx
shrd rax, r14, 56
add r8, rax
adc r10, 0x0
mov r14, r8
add r14, [ rsp + 0x120 ]
adc r10, 0x0
shrd rbp, rcx, 56
mov r9, [ rsp + 0xa8 ]
mov r13, r9
add r13, [ rsp + 0x100 ]
mov r12, [ rsp + 0xa0 ]
adcx r12, [ rsp + 0xf8 ]
test al, al
adox r13, rbp
adox r12, rdi
mov r9, r13
and r9, rdx
mov rcx, r14
shrd rcx, r10, 56
mov r11, rcx
test al, al
adox r11, [ rsp + 0x158 ]
mov rax, [ rsp + 0x150 ]
adox rax, rdi
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r9
shrd r13, r12, 56
add r13, [ rsp + 0x130 ]
mov r10, r13
shr r10, 56
mov rbp, r11
shrd rbp, rax, 56
mov r12, rbp
test al, al
adox r12, [ rsp + 0xf0 ]
mov r9, [ rsp + 0xe8 ]
adox r9, rdi
mov rcx, r12
shrd rcx, r9, 56
and r12, rdx
and r14, rdx
add rcx, [ rsp + 0x110 ]
mov rax, rcx
shr rax, 56
lea r15, [ r15 + rax ]
mov [ r8 + 0x30 ], r12
mov rbp, r15
and rbp, rdx
lea r14, [ r14 + rax ]
lea r10, [ r10 + r14 ]
mov r9, r10
and r9, rdx
and r11, rdx
and r13, rdx
shr r10, 56
lea r10, [ r10 + r11 ]
mov [ r8 + 0x28 ], r10
mov [ r8 + 0x18 ], r13
shr r15, 56
lea r15, [ r15 + rbx ]
mov [ r8 + 0x8 ], r15
and rcx, rdx
mov [ r8 + 0x0 ], rbp
mov [ r8 + 0x20 ], r9
mov [ r8 + 0x38 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 480
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0560
; seed 1434459832713540 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 19265 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=123, initial num_batches=31): 601 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.031196470282896443
; number reverted permutation / tried permutation: 343 / 531 =64.595%
; number reverted decision / tried decision: 273 / 468 =58.333%
; validated in 1.819s
