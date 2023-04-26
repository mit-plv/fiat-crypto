SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 336
mov rax, [ rsi + 0x38 ]
mov r10, rax
shl r10, 0x1
imul rax, [ rsi + 0x30 ], 0x2
imul r11, [ rsi + 0x20 ], 0x2
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rax
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, rdx
mov rdx, rbx
mov [ rsp - 0x18 ], r14
xor r14, r14
adox rdx, rcx
mov [ rsp - 0x10 ], r13
mov r13, r8
adox r13, r9
mov [ rsp - 0x8 ], rbp
mov rbp, rdx
adcx rbp, rbx
adcx r9, r13
xor rbx, rbx
adox rdx, rdi
mov r14, r15
adox r14, r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r12
mulx r12, rbx, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbx
mulx rbx, r12, r11
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp + 0x18 ], rbx
xor rbx, rbx
adox rbp, rcx
adox r8, r9
mulx r9, rcx, [ rsi + 0x18 ]
xchg rdx, rax
mov [ rsp + 0x20 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
adcx rbp, rdi
adcx r15, r8
mulx r8, rdi, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r8
xor r8, r8
adox rbp, rcx
mov [ rsp + 0x30 ], rdi
mov rdi, r9
adox rdi, r15
adcx r13, rcx
adcx r9, r14
test al, al
adox r13, rbx
mov r14, r12
adox r14, r9
mulx r15, rcx, [ rsi + 0x0 ]
adcx rbp, rbx
adcx r12, rdi
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rdi, rdx
test al, al
adox rbp, rdi
adox r9, r12
mov rdx, [ rsi + 0x0 ]
mulx rdi, r12, rdx
adcx r13, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
add r13, r12
adcx rdi, r14
mov rdx, [ rsi + 0x30 ]
mulx r14, r12, r10
xor rdx, rdx
adox rbp, [ rsp + 0x0 ]
adox r9, [ rsp - 0x8 ]
mov rdx, rax
mulx r8, rax, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], rdi
mov rdi, r12
adcx rdi, rax
mov [ rsp + 0x40 ], r13
mov r13, r8
adcx r13, r14
mov [ rsp + 0x48 ], r15
xor r15, r15
adox rdi, [ rsp + 0x30 ]
adox r13, [ rsp + 0x28 ]
mov [ rsp + 0x50 ], rcx
mov rcx, r12
adcx rcx, r12
adcx r14, r14
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r13
mulx r13, r15, rdx
add rcx, rax
adcx r8, r14
mov rdx, [ rsp - 0x10 ]
mov rax, rdx
add rax, rdx
mov r14, [ rsp - 0x18 ]
mov [ rsp + 0x60 ], rdi
mov rdi, r14
adcx rdi, r14
mov [ rsp + 0x68 ], r8
xor r8, r8
adox rax, r15
mov [ rsp + 0x70 ], rcx
mov rcx, r13
adox rcx, rdi
adcx rax, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r9
mulx r9, r8, rbx
mov rdx, r10
mov [ rsp + 0x80 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
test al, al
adox rdi, r15
adox r13, r14
adcx rax, r10
mov r14, rbp
adcx r14, rcx
mulx rcx, r15, [ rsi + 0x20 ]
test al, al
adox r8, r15
adox rcx, r9
mov r9, r8
adcx r9, [ rsp + 0x20 ]
mov r15, rcx
adcx r15, [ rsp + 0x18 ]
test al, al
adox rdi, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
adcx rdi, r10
adcx rbp, r13
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], rbp
mulx rbp, r13, rdx
imul rdx, [ rsi + 0x10 ], 0x2
add rax, r13
adcx rbp, r14
xchg rdx, rbx
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, r10
mov [ rsp + 0x90 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], rax
mulx rax, rbp, rbx
mov rdx, r12
mov [ rsp + 0xa8 ], rax
mulx rax, r12, [ rsi + 0x10 ]
test al, al
adox r9, r12
adox rax, r15
adcx r9, r14
adcx r13, rax
imul r15, [ rsi + 0x18 ], 0x2
add r9, r10
adcx rdi, r13
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, r10, rbx
test al, al
adox r8, r10
adox r12, rcx
mov rdx, r15
mulx rcx, r15, [ rsi + 0x0 ]
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, rax, r14
adcx r8, r15
adcx rcx, r12
mov rdx, 0xffffffffffffff 
mov r10, r8
and r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r12, r11
mov rdx, rbx
mov [ rsp + 0xb0 ], r10
mulx r10, rbx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rbp
mov rbp, rbx
adox rbp, [ rsp + 0x80 ]
adox r10, [ rsp + 0x78 ]
mov rbx, [ rsp + 0x30 ]
mov [ rsp + 0xc0 ], r13
mov r13, rbx
adcx r13, [ rsp + 0x70 ]
mov [ rsp + 0xc8 ], rax
mov rax, [ rsp + 0x28 ]
adcx rax, [ rsp + 0x68 ]
add rbp, r12
adcx r15, r10
shrd r8, rcx, 56
add r13, [ rsp - 0x30 ]
adcx rax, [ rsp - 0x38 ]
test al, al
adox rbp, r8
mov rbx, 0x0 
adox r15, rbx
mulx r12, rcx, [ rsi + 0x10 ]
mov rdx, 0x38 
bzhi r10, r9, rdx
adox r13, rcx
adox r12, rax
shrd r9, rdi, 56
add r13, [ rsp + 0x10 ]
adcx r12, [ rsp + 0x8 ]
mov rdi, r9
xor r8, r8
adox rdi, rbp
adox r15, r8
mov rbx, rdi
shrd rbx, r15, 56
mov rdx, r11
mulx rax, r11, [ rsi + 0x10 ]
imul rdx, [ rsi + 0x8 ], 0x2
mov rbp, r11
add rbp, [ rsp + 0xa0 ]
adcx rax, [ rsp + 0x98 ]
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, r14
mov rdx, [ rsp + 0x60 ]
add rdx, [ rsp - 0x30 ]
mov r14, [ rsp + 0x58 ]
adcx r14, [ rsp - 0x38 ]
add r13, r11
adcx r8, r12
xor r12, r12
adox r13, rbx
adox r8, r12
adcx rbp, [ rsp + 0xc8 ]
adcx rax, [ rsp + 0xc0 ]
mov rbx, r13
shrd rbx, r8, 56
test al, al
adox rbp, [ rsp + 0x50 ]
adox rax, [ rsp + 0x48 ]
adcx rbp, rbx
adc rax, 0x0
mov r11, rbp
shrd r11, rax, 56
add r9, [ rsp + 0x40 ]
mov r8, [ rsp + 0x38 ]
adc r8, 0x0
add rdx, rcx
adcx r15, r14
lea r11, [ r11 + r10 ]
mov r10, r9
shrd r10, r8, 56
mov rcx, [ rsp + 0x90 ]
xor r14, r14
adox rcx, [ rsp - 0x40 ]
mov r12, [ rsp + 0x88 ]
adox r12, [ rsp - 0x48 ]
adcx rdx, r10
adc r15, 0x0
mov rbx, 0xffffffffffffff 
and r9, rbx
mov rax, r11
and rax, rbx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x38 ], rax
shr r11, 56
lea r9, [ r9 + r11 ]
mov r10, r9
and r10, rbx
shr r9, 56
mov [ r8 + 0x0 ], r10
mov rax, rdx
and rax, rbx
shrd rdx, r15, 56
test al, al
adox rcx, [ rsp + 0xb8 ]
adox r12, [ rsp + 0xa8 ]
adcx rcx, rdx
adc r12, 0x0
mov r15, rcx
and r15, rbx
lea r9, [ r9 + rax ]
and rdi, rbx
shrd rcx, r12, 56
mov [ r8 + 0x8 ], r9
add rcx, [ rsp + 0xb0 ]
mov r10, rcx
and r10, rbx
shr rcx, 56
lea rdi, [ rdi + r11 ]
mov [ r8 + 0x18 ], r10
lea rcx, [ rcx + rdi ]
mov r11, rcx
and r11, rbx
mov [ r8 + 0x10 ], r15
mov [ r8 + 0x20 ], r11
shr rcx, 56
and rbp, rbx
and r13, rbx
lea rcx, [ rcx + r13 ]
mov [ r8 + 0x28 ], rcx
mov [ r8 + 0x30 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 336
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0694
; seed 0955773340459082 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3464923 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=110, initial num_batches=31): 113160 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03265873440766216
; number reverted permutation / tried permutation: 66565 / 89952 =74.001%
; number reverted decision / tried decision: 60822 / 90047 =67.545%
; validated in 1.956s
