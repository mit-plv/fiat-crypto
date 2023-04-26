SECTION .text
	GLOBAL fiat_p448_solinas_carry_mul
fiat_p448_solinas_carry_mul:
sub rsp, 472
mov rax, rdx
mov rdx, [ rdx + 0x38 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], r14
mulx r14, r13, [ rax + 0x38 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], r13
mulx r13, r14, [ rax + 0x38 ]
mov rdx, r9
test al, al
adox rdx, r10
mov [ rsp + 0x68 ], r13
mov r13, r11
adox r13, rbx
mov [ rsp + 0x70 ], r14
mov r14, rdx
adcx r14, r15
mov [ rsp + 0x78 ], r12
mov r12, rdi
adcx r12, r13
add rdx, r9
adcx rbx, r13
xor r9, r9
adox rdx, r10
adox r11, rbx
mov r10, rdx
mov rdx, [ rax + 0x18 ]
mulx rbx, r13, [ rsi + 0x30 ]
adcx r10, r15
adcx rdi, r11
xor rdx, rdx
adox r10, r13
mov r9, rbx
adox r9, rdi
mov rdx, [ rsi + 0x28 ]
mulx r11, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x80 ], rbp
mulx rbp, rdi, [ rsi + 0x20 ]
adcx r14, r13
adcx rbx, r12
add r14, r15
mov rdx, r11
adcx rdx, rbx
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, [ rax + 0x30 ]
test al, al
adox r10, r15
adox r11, r9
adcx r14, rdi
mov rdx, rbp
adcx rdx, r12
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mulx r12, r15, [ rax + 0x30 ]
xor rdx, rdx
adox r14, r13
mov [ rsp + 0x88 ], r8
mov r8, rbx
adox r8, r9
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x90 ], r8
mulx r8, r9, [ rsi + 0x38 ]
mov rdx, r9
adcx rdx, r15
mov [ rsp + 0x98 ], r14
mov r14, r12
adcx r14, r8
test al, al
adox r10, rdi
adox rbp, r11
adcx r10, r13
adcx rbx, rbp
test al, al
adox rdx, rcx
adox r14, [ rsp + 0x88 ]
mov rdi, rdx
adcx rdi, r9
adcx r8, r14
mov r13, rdx
mov rdx, [ rax + 0x38 ]
mulx r9, r11, [ rsi + 0x10 ]
add rdi, r15
adcx r12, r8
test al, al
adox rdi, rcx
adox r12, [ rsp + 0x88 ]
adcx r13, [ rsp + 0x80 ]
adcx r14, [ rsp + 0x78 ]
xor rdx, rdx
adox rdi, [ rsp + 0x80 ]
adox r12, [ rsp + 0x78 ]
mov rdx, [ rax + 0x18 ]
mulx r15, rcx, [ rsi + 0x28 ]
adcx r13, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
xor rdx, rdx
adox r10, r11
mov rbp, r9
adox rbp, rbx
mov rdx, [ rax + 0x38 ]
mulx r8, rbx, [ rsi + 0x38 ]
adcx r10, [ rsp - 0x40 ]
adcx rbp, [ rsp - 0x48 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xa0 ], rbp
mov [ rsp + 0xa8 ], r10
mulx r10, rbp, [ rsi + 0x28 ]
test al, al
adox r13, rcx
mov rdx, r15
adox rdx, r14
mov r14, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], r10
mulx r10, r13, [ rsi + 0x38 ]
mov rdx, r11
adcx rdx, [ rsp + 0x98 ]
adcx r9, [ rsp + 0x90 ]
xor r11, r11
adox rdi, [ rsp - 0x20 ]
adox r12, [ rsp - 0x28 ]
adcx rdx, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], r9
mov [ rsp + 0xc8 ], r14
mulx r14, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xd0 ], r11
mov [ rsp + 0xd8 ], rbp
mulx rbp, r11, [ rsi + 0x18 ]
xor rdx, rdx
adox rdi, rcx
adox r15, r12
mov rcx, rbx
adcx rcx, r13
mov r12, r10
adcx r12, r8
add rcx, r9
mov [ rsp + 0xe0 ], rbp
mov rbp, r14
adcx rbp, r12
mov r12, rbx
test al, al
adox r12, rbx
adox r8, r8
adcx rcx, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0xb8 ]
xor rbx, rbx
adox r12, r13
adox r10, r8
mov rdx, [ rsi + 0x20 ]
mulx r8, r13, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rbp
mulx rbp, rbx, [ rax + 0x30 ]
adcx r12, r9
adcx r14, r10
mov rdx, r13
add rdx, [ rsp + 0xb0 ]
mov r9, r8
adcx r9, [ rsp + 0xc8 ]
xor r10, r10
adox rdi, r13
adox r8, r15
adcx r12, [ rsp + 0xd8 ]
adcx r14, [ rsp + 0xb8 ]
add rdi, r11
adcx r8, [ rsp + 0xe0 ]
add rdx, r11
adcx r9, [ rsp + 0xe0 ]
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf0 ], r9
mulx r9, r10, [ rsi + 0x30 ]
test al, al
adox rdi, [ rsp + 0x20 ]
adox r8, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r14
mulx r14, r11, [ rax + 0x20 ]
adcx r11, r10
adcx r9, r14
add r11, r15
adcx r13, r9
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rax + 0x0 ]
xor rdx, rdx
adox rdi, [ rsp + 0x70 ]
adox r8, [ rsp + 0x68 ]
mov rdx, [ rax + 0x38 ]
mulx r9, r14, [ rsi + 0x20 ]
adcx rcx, rbx
mov rdx, rbp
adcx rdx, [ rsp + 0xe8 ]
test al, al
adox r11, r14
adox r9, r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x108 ], r8
mulx r8, r14, [ rax + 0x8 ]
adcx r12, rbx
adcx rbp, [ rsp + 0x100 ]
xor rdx, rdx
adox rcx, [ rsp + 0x60 ]
adox r13, [ rsp + 0x58 ]
adcx r12, [ rsp + 0x60 ]
adcx rbp, [ rsp + 0x58 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x110 ], r13
mulx r13, rbx, [ rsi + 0x38 ]
mov rdx, r11
mov [ rsp + 0x118 ], rcx
xor rcx, rcx
adox rdx, rbx
adox r13, r9
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x120 ], rbp
mulx rbp, rcx, [ rsi + 0x30 ]
adcx r11, r15
adcx r10, r9
xor rdx, rdx
adox r11, r14
adox r8, r10
mov rdx, [ rsi + 0x10 ]
mulx r9, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r14, [ rsi + 0x0 ]
adcx r11, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
test al, al
adox r11, r14
adox r10, r8
mov rdx, [ rax + 0x10 ]
mulx r8, r14, [ rsi + 0x28 ]
adcx rbx, rcx
adcx rbp, r13
mov rdx, [ rax + 0x8 ]
mulx rcx, r13, [ rsi + 0x18 ]
test al, al
adox rbx, r14
adox r8, rbp
mov rdx, [ rax + 0x0 ]
mulx rbp, r14, [ rsi + 0x20 ]
adcx rdi, r14
adcx rbp, [ rsp + 0x108 ]
mov rdx, 0x38 
bzhi r14, r11, rdx
adox rdi, r13
adox rcx, rbp
add rdi, r15
adcx r9, rcx
mov rdx, [ rax + 0x20 ]
mulx r13, r15, [ rsi + 0x0 ]
shrd r11, r10, 56
mov rdx, [ rsi + 0x20 ]
mulx rbp, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], r14
mulx r14, rcx, [ rax + 0x20 ]
xor rdx, rdx
adox rbx, r10
adox rbp, r8
mov rdx, [ rsi + 0x20 ]
mulx r10, r8, [ rax + 0x8 ]
adcx rbx, rcx
adcx r14, rbp
test al, al
adox rdi, [ rsp + 0x40 ]
adox r9, [ rsp + 0x38 ]
mov rdx, r8
adcx rdx, [ rsp + 0xa8 ]
adcx r10, [ rsp + 0xa0 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, [ rax + 0x10 ]
add rcx, rbp
adcx r8, r10
test al, al
adox rcx, [ rsp + 0x50 ]
adox r8, [ rsp + 0x48 ]
adcx rdi, r15
adcx r13, r9
mov rdx, [ rsi + 0x30 ]
mulx r9, r15, [ rax + 0x0 ]
test al, al
adox r12, r15
adox r9, [ rsp + 0x120 ]
mov rdx, [ rax + 0x28 ]
mulx rbp, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x130 ], r13
mulx r13, r15, [ rsi + 0x28 ]
adcx r12, r15
adcx r13, r9
mov rdx, [ rsi + 0x8 ]
mulx r15, r9, [ rax + 0x20 ]
add rbx, r10
adcx rbp, r14
mov rdx, [ rsi + 0x8 ]
mulx r10, r14, [ rax + 0x28 ]
test al, al
adox r12, [ rsp + 0x0 ]
adox r13, [ rsp - 0x8 ]
adcx rbx, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x138 ], r10
mov [ rsp + 0x140 ], r14
mulx r14, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, r10
adox r14, rbp
adcx rcx, r9
adcx r15, r8
mov r8, rbx
shrd r8, r14, 56
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r14, r10, [ rsi + 0x18 ]
test al, al
adox r12, r10
adox r14, r13
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x148 ], rbp
mov [ rsp + 0x150 ], r9
mulx r9, rbp, [ rsi + 0x10 ]
adcx rdi, r11
mov rdx, [ rsp + 0x130 ]
adc rdx, 0x0
add r12, rbp
adcx r9, r14
add r12, [ rsp + 0x140 ]
adcx r9, [ rsp + 0x138 ]
test al, al
adox r12, r13
adox r10, r9
mov r11, r8
adcx r11, rdi
adc rdx, 0x0
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r13, [ rax + 0x28 ]
mov rdx, r11
shrd rdx, r14, 56
mov rdi, [ rsp + 0xf8 ]
add rdi, [ rsp + 0x20 ]
mov r9, [ rsp + 0xf0 ]
adcx r9, [ rsp + 0x18 ]
xor r14, r14
adox rcx, r13
adox rbp, r15
adcx rcx, rdx
adc rbp, 0x0
mov rdx, [ rax + 0x8 ]
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, rcx
shrd rdx, rbp, 56
test al, al
adox r12, rdx
adox r10, r14
mov rbp, 0xffffffffffffff 
mov rdx, r12
and rdx, rbp
shrd r12, r10, 56
and rbx, rbp
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x30 ], rdx
adox rdi, [ rsp + 0x70 ]
adox r9, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r14, [ rax + 0x0 ]
mov rdx, r14
adcx rdx, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x110 ]
xor r14, r14
adox rdi, [ rsp + 0x150 ]
adox r9, [ rsp + 0x148 ]
lea r12, [ r12 + rbx ]
adcx r8, rdi
adc r9, 0x0
mov rbx, r8
shrd rbx, r9, 56
mov rdi, r12
shr rdi, 56
mov r9, r15
add r9, [ rsp + 0xd0 ]
adcx r13, [ rsp + 0xc0 ]
xor r15, r15
adox r9, rbx
adox r13, r15
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, rbx, [ rsi + 0x8 ]
adcx r14, rbx
adcx r15, rbp
mov rdx, 0xffffffffffffff 
and r12, rdx
mov rbp, r9
shrd rbp, r13, 56
mov [ r10 + 0x38 ], r12
test al, al
adox r14, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
adcx r14, rbp
adc r15, 0x0
mov r13, r14
shrd r13, r15, 56
add r13, [ rsp + 0x128 ]
mov rbx, r13
shr rbx, 56
and r13, rdx
and r11, rdx
and rcx, rdx
lea r11, [ r11 + rdi ]
lea rbx, [ rbx + r11 ]
and r8, rdx
mov r12, rbx
shr r12, 56
lea r8, [ r8 + rdi ]
mov rdi, r8
and rdi, rdx
lea r12, [ r12 + rcx ]
mov [ r10 + 0x18 ], r13
mov [ r10 + 0x28 ], r12
and r9, rdx
shr r8, 56
and rbx, rdx
lea r8, [ r8 + r9 ]
and r14, rdx
mov [ r10 + 0x20 ], rbx
mov [ r10 + 0x8 ], r8
mov [ r10 + 0x10 ], r14
mov [ r10 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 472
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2727
; seed 1337930511914402 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8496616 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=51, initial num_batches=31): 201214 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.023681663382221815
; number reverted permutation / tried permutation: 64750 / 90255 =71.741%
; number reverted decision / tried decision: 50008 / 89744 =55.723%
; validated in 4.89s
