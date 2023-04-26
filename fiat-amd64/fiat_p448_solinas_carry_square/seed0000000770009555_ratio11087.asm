SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 408
imul rax, [ rsi + 0x10 ], 0x2
mov r10, [ rsi + 0x28 ]
mov r11, r10
shl r11, 0x1
imul r10, [ rsi + 0x30 ], 0x2
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, rdx
mov rdx, r10
mulx r9, r10, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, rax
mov rdx, r14
mov [ rsp - 0x38 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rdi
mov rdi, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r14
lea r14, [rdi + rdi]
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r9
mulx r9, rdi, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], rbp
mulx rbp, r10, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r10
mulx r10, rbp, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r10
mulx r10, r14, r15
imul rdx, [ rsi + 0x8 ], 0x2
mov r15, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r10
lea r10, [r15 + r15]
mov [ rsp + 0x30 ], r14
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], r14
mulx r14, rbp, r11
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x48 ], r15
mov r15, rdx
shl r15, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], rbx
mov [ rsp + 0x58 ], r14
mulx r14, rbx, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], rbp
mov [ rsp + 0x68 ], r10
mulx r10, rbp, r11
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], r10
mov [ rsp + 0x78 ], rbp
mulx rbp, r10, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], r10
mulx r10, rbp, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], r10
mov [ rsp + 0x98 ], rbp
mulx rbp, r10, r15
xor rdx, rdx
adox r12, rbx
adox r14, r13
mov r13, r12
adcx r13, r8
adcx rcx, r14
mov rdx, [ rsi + 0x20 ]
mulx rbx, r8, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa0 ], rbp
mov [ rsp + 0xa8 ], r10
mulx r10, rbp, r15
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], rbp
mulx rbp, r10, rdx
test al, al
adox r13, rdi
adox r9, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rdi, [ rsp + 0x68 ]
adcx r12, rdi
adcx rcx, r14
mov rdx, r11
mulx r14, r11, [ rsi + 0x8 ]
mov rdi, r10
mov [ rsp + 0xc0 ], r14
xor r14, r14
adox rdi, [ rsp + 0x88 ]
mov [ rsp + 0xc8 ], r11
mov r11, rbp
adox r11, [ rsp + 0x80 ]
mov [ rsp + 0xd0 ], r9
mov r9, rdi
adcx r9, r10
adcx rbp, r11
xor r10, r10
adox rdi, r8
mov r14, rbx
adox r14, r11
xchg rdx, r15
mulx r10, r11, [ rsi + 0x0 ]
adcx r12, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x58 ]
add r12, [ rsp + 0x50 ]
adcx rcx, [ rsp + 0x8 ]
mov [ rsp + 0xd8 ], r13
xor r13, r13
adox r12, r11
adox r10, rcx
adcx r9, [ rsp + 0x88 ]
adcx rbp, [ rsp + 0x80 ]
mov r11, r12
shrd r11, r10, 56
add r9, r8
adcx rbx, rbp
mov r8, 0x38 
bzhi rcx, r12, r8
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, r15
adox rdi, r10
mov rdx, rbp
adox rdx, r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r13, rdx
mov rdx, 0x38 
mov [ rsp + 0xe0 ], rcx
bzhi rcx, [ rsp + 0xd8 ], rdx
adox r9, r10
adox rbp, rbx
mov rdx, [ rsi + 0x28 ]
mulx r10, rbx, rdx
xor rdx, rdx
adox r9, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
adcx r9, r13
adcx r8, rbp
mov rdx, [ rsi + 0x20 ]
mulx rbp, r13, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], rcx
mulx rcx, r15, r12
add rdi, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
test al, al
adox rdi, r15
mov rdx, rcx
adox rdx, r14
mov r12, rbx
adcx r12, [ rsp - 0x20 ]
mov r14, r10
adcx r14, [ rsp - 0x38 ]
mov [ rsp + 0xf0 ], rax
xor rax, rax
adox r9, r15
adox rcx, r8
mov r8, [ rsp - 0x20 ]
mov r15, r8
adcx r15, r8
mov [ rsp + 0xf8 ], rcx
mov rcx, [ rsp - 0x38 ]
adcx rcx, rcx
xor r8, r8
adox r15, rbx
adox r10, rcx
adcx r15, [ rsp - 0x28 ]
adcx r10, [ rsp - 0x30 ]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbx, rdx
add rdi, rbx
adcx rcx, rax
mov rdx, r11
xor rax, rax
adox rdx, rdi
adox rcx, rax
adcx r12, [ rsp - 0x28 ]
adcx r14, [ rsp - 0x30 ]
mov r8, [ rsp + 0xb8 ]
mov rbx, r8
xor rdi, rdi
adox rbx, r8
mov rax, [ rsp + 0xb0 ]
mov [ rsp + 0x100 ], r14
mov r14, rax
adox r14, rax
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r12
mov [ rsp + 0x110 ], rcx
mulx rcx, r12, [ rsp + 0x68 ]
adcx rbx, r13
mov rdx, rbp
adcx rdx, r14
test al, al
adox r8, r13
adox rbp, rax
adcx r8, [ rsp - 0x10 ]
adcx rbp, [ rsp - 0x18 ]
mov rax, [ rsp + 0xd8 ]
mov r13, [ rsp + 0xd0 ]
shrd rax, r13, 56
xor r13, r13
adox r9, [ rsp + 0x18 ]
mov r14, [ rsp + 0xf8 ]
adox r14, [ rsp + 0x10 ]
adcx r9, r12
adcx rcx, r14
xor r12, r12
adox r9, rax
adox rcx, r12
adcx r15, [ rsp + 0xa8 ]
adcx r10, [ rsp + 0xa0 ]
mov r13, [ rsp + 0x110 ]
mov rax, rdi
shrd rax, r13, 56
xor r13, r13
adox r11, r9
adox rcx, r13
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r14, rdx
adcx r8, [ rsp + 0x98 ]
adcx rbp, [ rsp + 0x90 ]
xor rdx, rdx
adox r15, r14
adox r9, r10
adcx r8, [ rsp + 0x48 ]
adcx rbp, [ rsp + 0x40 ]
xor r13, r13
adox rbx, [ rsp - 0x10 ]
adox r12, [ rsp - 0x18 ]
adcx rbx, [ rsp + 0x98 ]
adcx r12, [ rsp + 0x90 ]
xor rdx, rdx
adox r8, rax
adox rbp, rdx
mov rdx, [ rsp + 0x68 ]
mulx r10, r13, [ rsi + 0x8 ]
adcx rbx, [ rsp + 0x38 ]
adcx r12, [ rsp + 0x20 ]
xor rax, rax
adox rbx, r13
adox r10, r12
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, r11
shrd rdx, rcx, 56
xor rcx, rcx
adox rbx, [ rsp + 0x78 ]
adox r10, [ rsp + 0x70 ]
adcx r15, r14
adcx r13, r9
xor rax, rax
adox rbx, rdx
adox r10, rax
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ rsp + 0xf0 ]
adcx r15, [ rsp + 0xc8 ]
adcx r13, [ rsp + 0xc0 ]
add r15, [ rsp + 0x30 ]
adcx r13, [ rsp + 0x28 ]
mov rdx, rbx
shrd rdx, r10, 56
mov r12, [ rsp + 0x108 ]
add r12, [ rsp + 0xa8 ]
mov r14, [ rsp + 0x100 ]
adcx r14, [ rsp + 0xa0 ]
xor r10, r10
adox r15, rdx
adox r13, r10
mov rax, r15
shrd rax, r13, 56
mov rdx, 0x38 
bzhi r13, rbx, rdx
adox r12, [ rsp - 0x40 ]
adox r14, [ rsp - 0x48 ]
add rax, [ rsp + 0xe0 ]
xor rbx, rbx
adox r12, rcx
adox r9, r14
bzhi r10, rax, rdx
bzhi rcx, rdi, rdx
shr rax, 56
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x38 ], r10
lea rcx, [ rcx + rax ]
mov r14, r8
shrd r14, rbp, 56
xor rbp, rbp
adox r12, r14
adox r9, rbp
mov rbx, r12
shrd rbx, r9, 56
bzhi r10, r11, rdx
bzhi r11, r12, rdx
mov [ rdi + 0x10 ], r11
add rbx, [ rsp + 0xe8 ]
bzhi r14, rbx, rdx
lea r10, [ r10 + rax ]
mov [ rdi + 0x18 ], r14
shr rbx, 56
lea rbx, [ rbx + r10 ]
bzhi rax, r15, rdx
bzhi r15, rcx, rdx
bzhi r12, rbx, rdx
shr rbx, 56
lea rbx, [ rbx + r13 ]
mov [ rdi + 0x0 ], r15
bzhi r13, r8, rdx
shr rcx, 56
mov [ rdi + 0x28 ], rbx
lea rcx, [ rcx + r13 ]
mov [ rdi + 0x8 ], rcx
mov [ rdi + 0x20 ], r12
mov [ rdi + 0x30 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 408
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1087
; seed 0315900068712740 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3108685 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=137, initial num_batches=31): 107134 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.034462803404011665
; number reverted permutation / tried permutation: 65810 / 90270 =72.904%
; number reverted decision / tried decision: 59893 / 89729 =66.749%
; validated in 2.101s
