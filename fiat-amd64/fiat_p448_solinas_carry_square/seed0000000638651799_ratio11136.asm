SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 416
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x38 ], 0x2
mov rdx, [ rsi + 0x8 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, r11
mulx r8, r11, [ rsi + 0x28 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
lea rdi, [rdx + rdx]
mov rdx, rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rdi
mulx rdi, rcx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r14
mov r14, r12
test al, al
adox r14, r12
mov [ rsp - 0x18 ], r15
mov r15, r13
adox r15, r13
adcx r14, rbx
mov [ rsp - 0x10 ], rdi
mov rdi, rbp
adcx rdi, r15
mov r15, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rcx
mov rcx, r15
shl rcx, 0x1
mov r15, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], rcx
mov rcx, r15
shl rcx, 0x1
xor r15, r15
adox r12, rbx
adox rbp, r13
xchg rdx, rcx
mulx r13, rbx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], r13
mulx r13, rbx, [ rsi + 0x20 ]
adcx r12, rbx
mov [ rsp + 0x20 ], r15
mov r15, r13
adcx r15, rbp
mov [ rsp + 0x28 ], r15
mulx r15, rbp, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], r12
mulx r12, rbp, rdx
mov rdx, rbp
mov [ rsp + 0x48 ], r10
xor r10, r10
adox rdx, r11
mov [ rsp + 0x50 ], rax
mov rax, r8
adox rax, r12
adcx r14, rbx
adcx r13, rdi
mov rdi, rdx
xor rbx, rbx
adox rdi, [ rsp + 0x50 ]
mov r10, rax
adox r10, [ rsp + 0x48 ]
adcx rdx, rbp
adcx r12, rax
mov rbp, [ rsi + 0x20 ]
mov rax, rbp
shl rax, 0x1
xor rbp, rbp
adox rdx, r11
adox r8, r12
adcx rdx, [ rsp + 0x50 ]
adcx r8, [ rsp + 0x48 ]
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mulx r12, r11, r9
mov rdx, r11
test al, al
adox rdx, r11
mov [ rsp + 0x58 ], r13
mov r13, r12
adox r13, r12
adcx rbx, [ rsp - 0x8 ]
adcx r8, [ rsp - 0x10 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r14
mov [ rsp + 0x68 ], r8
mulx r8, r14, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r14
mulx r14, r8, rax
test al, al
adox rdi, [ rsp - 0x8 ]
adox r10, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x18 ]
adcx r12, [ rsp - 0x20 ]
add rbp, [ rsp - 0x18 ]
adcx r13, [ rsp - 0x20 ]
add r11, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x18 ]
test al, al
adox rbp, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
mov rdx, r15
mov [ rsp + 0x80 ], r10
mulx r10, r15, [ rsi + 0x28 ]
adcx r11, [ rsp - 0x28 ]
adcx r12, [ rsp - 0x30 ]
xchg rdx, r9
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r11
mulx r11, r12, [ rsi + 0x20 ]
add r15, r12
adcx r11, r10
mov r10, r15
test al, al
adox r10, r8
adox r14, r11
adcx r10, [ rsp - 0x38 ]
adcx r14, [ rsp - 0x40 ]
imul r8, [ rsi + 0x18 ], 0x2
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], rdi
mov [ rsp + 0xa0 ], rbx
mulx rbx, rdi, r8
mov rdx, r8
mov [ rsp + 0xa8 ], rbx
mulx rbx, r8, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r8
mulx r8, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], rbx
mulx rbx, r8, [ rsp + 0x0 ]
test al, al
adox r15, r8
adox rbx, r11
adcx r10, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, r12
add r10, r11
adcx r8, r14
xor rdx, rdx
adox rbp, [ rsp - 0x28 ]
adox r13, [ rsp - 0x30 ]
adcx r15, [ rsp + 0xc0 ]
adcx rbx, [ rsp + 0xb8 ]
mov r14, 0xffffffffffffff 
mov r11, r15
and r11, r14
shrd r15, rbx, 56
test al, al
adox rbp, [ rsp + 0xb0 ]
adox r13, [ rsp + 0xa8 ]
mov rdx, r9
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, r9
adcx rdx, [ rsp + 0xa0 ]
mov r14, rbx
adcx r14, [ rsp + 0x68 ]
add rdx, [ rsp + 0xd0 ]
adcx r14, [ rsp + 0xc8 ]
mov [ rsp + 0xd8 ], r11
mov r11, 0xffffffffffffff 
mov [ rsp + 0xe0 ], r13
mov r13, r10
and r13, r11
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r13
mov [ rsp + 0xf0 ], rbp
mulx rbp, r13, r12
adox r11, r13
mov rdx, rbp
adox rdx, r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], rcx
mov [ rsp + 0x100 ], r15
mulx r15, rcx, rdi
adcx r11, rcx
adcx r15, r14
mov rdx, r9
xor rdi, rdi
adox rdx, [ rsp + 0x98 ]
adox rbx, [ rsp + 0x80 ]
adcx rdx, r13
adcx rbp, rbx
test al, al
adox r11, [ rsp + 0x78 ]
adox r15, [ rsp + 0x70 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r13, rdx
mov rdx, [ rsp - 0x48 ]
mulx rbx, rcx, [ rsi + 0x0 ]
adcx r11, [ rsp + 0x100 ]
adc r15, 0x0
shrd r10, r8, 56
xor rdx, rdx
adox r9, r13
adox r14, rbp
mov rdx, r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, r10
adcx rdx, r9
adc r14, 0x0
add r10, r11
adc r15, 0x0
mov r8, rdi
add r8, [ rsp + 0x60 ]
mov rbp, r12
adcx rbp, [ rsp + 0x58 ]
mov r13, r10
shrd r13, r15, 56
mov r11, rcx
xor r9, r9
adox r11, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x88 ]
mov rcx, 0x38 
bzhi r15, rdx, rcx
shrd rdx, r14, 56
test al, al
adox r11, rdx
adox rbx, r9
bzhi r14, r10, rcx
mov r10, r11
shrd r10, rbx, 56
mov rdx, rdi
test al, al
adox rdx, [ rsp + 0x40 ]
adox r12, [ rsp + 0x28 ]
bzhi rdi, r11, rcx
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, rbx, rdx
mov rdx, rax
mulx rcx, rax, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], r15
mov [ rsp + 0x118 ], r14
mulx r14, r15, [ rsp + 0x0 ]
adox r11, rbx
adox r9, r12
mov rdx, [ rsi + 0x18 ]
mulx rbx, r12, rdx
add r8, r12
adcx rbx, rbp
xor rdx, rdx
adox r11, r15
adox r14, r9
mov rdx, [ rsi + 0x10 ]
mulx r15, rbp, rdi
adcx r8, rbp
adcx r15, rbx
xor rdx, rdx
adox r11, r10
adox r14, rdx
mov rdx, [ rsp + 0xf8 ]
mulx r10, rdi, [ rsi + 0x8 ]
adcx r8, rdi
adcx r10, r15
mov r9, 0xffffffffffffff 
mov r12, r11
and r12, r9
shrd r11, r14, 56
mov rbx, rax
test al, al
adox rbx, [ rsp + 0xf0 ]
adox rcx, [ rsp + 0xe0 ]
add r11, [ rsp + 0xd8 ]
mulx rbp, rax, [ rsi + 0x0 ]
add rbx, rax
adcx rbp, rcx
xor rdx, rdx
adox rbx, r13
adox rbp, rdx
mov r13, r11
and r13, r9
shr r11, 56
mov r15, rbx
shrd r15, rbp, 56
add r8, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x30 ]
add r8, r15
adc r10, 0x0
mov r14, r8
shrd r14, r10, 56
add r14, [ rsp + 0xe8 ]
mov rdi, r14
shr rdi, 56
and r8, r9
mov rcx, rdi
add rcx, [ rsp + 0x118 ]
lea r11, [ r11 + rcx ]
mov rax, r11
and rax, r9
add rdi, [ rsp + 0x110 ]
mov rbp, rdi
shr rbp, 56
and rdi, r9
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], rdi
add rbp, [ rsp + 0x108 ]
mov [ r15 + 0x8 ], rbp
shr r11, 56
and rbx, r9
lea r11, [ r11 + rbx ]
mov [ r15 + 0x10 ], r12
and r14, r9
mov [ r15 + 0x38 ], r14
mov [ r15 + 0x20 ], rax
mov [ r15 + 0x18 ], r13
mov [ r15 + 0x28 ], r11
mov [ r15 + 0x30 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 416
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1136
; seed 1443210922192440 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2486219 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=196, initial num_batches=31): 104079 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04186236208475601
; number reverted permutation / tried permutation: 71957 / 90172 =79.800%
; number reverted decision / tried decision: 65140 / 89827 =72.517%
; validated in 1.016s
