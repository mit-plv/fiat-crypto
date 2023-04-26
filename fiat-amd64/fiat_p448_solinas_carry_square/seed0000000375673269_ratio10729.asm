SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 368
mov rax, 0x1 
shlx r10, [ rsi + 0x38 ], rax
shlx r11, [ rsi + 0x10 ], rax
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
shlx rdx, [ rsi + 0x18 ], rax
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, rdx
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov rdi, rdx
shl rdi, 0x1
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rax
mulx rax, rbx, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rdi
mulx rdi, r11, r9
mov rdx, r10
mov [ rsp - 0x18 ], rdi
mulx rdi, r10, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r10
mulx r10, rdi, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], rdi
mulx rdi, r10, r9
mov rdx, r9
mov [ rsp + 0x18 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], r10
mulx r10, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], r9
mov r9, r14
test al, al
adox r9, r13
mov [ rsp + 0x48 ], rax
mov rax, r12
adox rax, r15
mov [ rsp + 0x50 ], rbx
mov rbx, r9
adcx rbx, r14
adcx r15, rax
add rbx, r13
adcx r12, r15
mulx r13, r14, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r13
mulx r13, r15, [ rsi + 0x8 ]
add r9, rcx
mov [ rsp + 0x60 ], r14
mov r14, r8
adcx r14, rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], r15
mulx r15, r13, r11
xor rdx, rdx
adox rdi, r13
adox r15, r10
adcx rbx, rcx
adcx r8, r12
add rbx, [ rsp + 0x50 ]
adcx r8, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, rcx, rax
mov rdx, [ rsi + 0x10 ]
mulx r13, r12, rdx
mov rdx, rbp
mov [ rsp + 0x78 ], r15
mulx r15, rbp, [ rsi + 0x0 ]
add rbx, rcx
mov [ rsp + 0x80 ], r15
mov r15, r10
adcx r15, r8
mov [ rsp + 0x88 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
test al, al
adox rbx, r12
adox r13, r15
adcx rbx, [ rsp + 0x0 ]
adcx r13, [ rsp - 0x8 ]
test al, al
adox rbx, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
adcx r9, [ rsp + 0x50 ]
adcx r14, [ rsp + 0x48 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], rbp
mulx rbp, r15, [ rsp - 0x20 ]
mov rdx, rdi
mov [ rsp + 0x98 ], r8
xor r8, r8
adox rdx, r15
adox rbp, [ rsp + 0x78 ]
adcx r9, rcx
adcx r10, r14
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, [ rsp - 0x28 ]
add r9, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x8 ]
add rdi, r14
adcx r15, [ rsp + 0x78 ]
xor rdx, rdx
adox rdi, [ rsp + 0x40 ]
adox r15, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, rdx
mov rdx, r12
mov [ rsp + 0xa0 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, r11
mov [ rsp + 0xa8 ], rbx
mulx rbx, r11, [ rsi + 0x0 ]
adcx rcx, r12
adcx r13, rbp
add rcx, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x68 ]
test al, al
adox r9, r8
adox r14, r10
mov rbp, 0x38 
bzhi r10, rdi, rbp
adox rcx, r11
adox rbx, r13
mov r8, rcx
shrd r8, rbx, 56
shrd rdi, r15, 56
mulx r12, r15, [ rsi + 0x18 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r13, rax
mov rdx, [ rsi + 0x38 ]
mulx rbp, rax, rdx
mov rdx, rax
add rdx, rax
mov [ rsp + 0xb0 ], r10
mov r10, rbp
adcx r10, rbp
mov [ rsp + 0xb8 ], rdi
mov rdi, r8
mov [ rsp + 0xc0 ], r12
xor r12, r12
adox rdi, r9
adox r14, r12
mov r9, rdi
shrd r9, r14, 56
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], r9
mulx r9, r12, rdx
test al, al
adox rax, r12
mov rdx, r9
adox rdx, rbp
adcx rax, r13
mov rbp, rbx
adcx rbp, rdx
test al, al
adox r14, r12
adox r9, r10
adcx rax, r15
adcx rbp, [ rsp + 0xc0 ]
imul r10, [ rsi + 0x8 ], 0x2
mov rdx, r10
mulx r12, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, r13
adox rbx, r9
adcx r14, r15
adcx rbx, [ rsp + 0xc0 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], rbp
mulx rbp, r9, [ rsp - 0x20 ]
test al, al
adox r14, r15
adox r13, rbx
mov rdx, r9
adcx rdx, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0xa0 ]
xchg rdx, r11
mulx r15, rbx, [ rsi + 0x30 ]
mov rdx, rbx
xor r9, r9
adox rdx, rbx
mov [ rsp + 0xd8 ], r13
mov r13, r15
adox r13, r15
adcx rbx, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x8 ]
test al, al
adox rbx, [ rsp + 0x60 ]
adox r15, [ rsp + 0x58 ]
adcx rbx, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
test al, al
adox r11, [ rsp + 0xb8 ]
adox rbp, r9
adcx r8, r11
adc rbp, 0x0
add rbx, r10
adcx r12, r15
add rbx, [ rsp + 0xc8 ]
adc r12, 0x0
xor r10, r10
adox rdx, [ rsp + 0x10 ]
adox r13, [ rsp + 0x8 ]
mov r9, r8
shrd r9, rbp, 56
mov r15, rbx
shrd r15, r12, 56
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, [ rsp - 0x28 ]
add rax, [ rsp - 0x40 ]
mov rdx, [ rsp + 0xd0 ]
adcx rdx, [ rsp - 0x48 ]
test al, al
adox r11, [ rsp + 0x60 ]
adox r13, [ rsp + 0x58 ]
adcx r11, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
test al, al
adox r11, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
adcx rax, rbp
adcx r12, rdx
mov rdx, [ rsp - 0x20 ]
mulx r10, rbp, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], r14
xor r14, r14
adox rax, r15
adox r12, r14
mulx r14, r15, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffff 
mov [ rsp + 0xe8 ], r10
mov r10, rax
and r10, rdx
shrd rax, r12, 56
xor r12, r12
adox r11, r15
adox r14, r13
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], r10
adcx r11, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x80 ]
add r11, r9
adc r14, 0x0
and rcx, rdx
mov r9, r11
shrd r9, r14, 56
mov r15, rbp
add r15, [ rsp + 0xe0 ]
mov r10, [ rsp + 0xd8 ]
adcx r10, [ rsp + 0xe8 ]
test al, al
adox r15, [ rsp + 0x98 ]
adox r10, [ rsp + 0x90 ]
adcx r15, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x30 ]
xor rbp, rbp
adox r15, r9
adox r10, rbp
and r11, rdx
mov r12, r15
shrd r12, r10, 56
lea r12, [ r12 + rcx ]
mov r14, r12
shr r14, 56
and rdi, rdx
and r12, rdx
and r15, rdx
and r8, rdx
lea r8, [ r8 + r14 ]
lea rdi, [ rdi + r14 ]
mov rcx, rdi
and rcx, rdx
mov [ r13 + 0x0 ], rcx
add rax, [ rsp + 0xb0 ]
and rbx, rdx
shr rdi, 56
mov r9, rax
and r9, rdx
shr rax, 56
lea rax, [ rax + r8 ]
mov r10, rax
and r10, rdx
mov [ r13 + 0x20 ], r10
lea rdi, [ rdi + rbx ]
shr rax, 56
lea rax, [ rax + r11 ]
mov [ r13 + 0x28 ], rax
mov [ r13 + 0x18 ], r9
mov [ r13 + 0x30 ], r15
mov [ r13 + 0x38 ], r12
mov [ r13 + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 368
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0729
; seed 0032040454542023 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5580180 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 174917 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03134612145127935
; number reverted permutation / tried permutation: 65564 / 90214 =72.676%
; number reverted decision / tried decision: 60039 / 89785 =66.870%
; validated in 1.684s
