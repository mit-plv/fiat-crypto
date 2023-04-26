SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 432
mov rdx, [ rsi + 0x28 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x38 ]
mulx rcx, r11, rdx
mov rdx, 0x1 
shlx r8, [ rsi + 0x30 ], rdx
mov r9, r11
test al, al
adox r9, r11
mov rdx, rcx
adox rdx, rcx
mov [ rsp - 0x80 ], rbx
imul rbx, [ rsi + 0x18 ], 0x2
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rdx
mov rdx, r8
mov [ rsp - 0x40 ], r14
mulx r14, r8, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r14
mov r14, 0x1 
mov [ rsp - 0x30 ], r8
shlx r8, [ rsi + 0x20 ], r14
mov [ rsp - 0x28 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r13
mov r13, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r14
lea r14, [r13 + r13]
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r12
mov r12, [ rsi + 0x38 ]
mov [ rsp + 0x0 ], r8
lea r8, [r12 + r12]
mov r12, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r14
mov r14, r12
shl r14, 0x1
xchg rdx, r8
mov [ rsp + 0x10 ], r14
mulx r14, r12, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r14
xor r14, r14
adox r9, rax
mov [ rsp + 0x20 ], r12
mov r12, r10
adox r12, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r12
mulx r12, r14, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r9
mov [ rsp + 0x38 ], r13
mulx r13, r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r15
mov [ rsp + 0x48 ], rdi
mulx rdi, r15, rbp
mov rdx, rbp
mov [ rsp + 0x50 ], r13
mulx r13, rbp, [ rsi + 0x28 ]
adcx r14, r15
adcx rdi, r12
mov r12, r9
test al, al
adox r12, rbp
mov r15, r13
adox r15, [ rsp + 0x50 ]
mov [ rsp + 0x58 ], rdi
mov rdi, r12
adcx rdi, r9
mov [ rsp + 0x60 ], r14
mov r14, r15
adcx r14, [ rsp + 0x50 ]
add rdi, rbp
adcx r13, r14
add r12, [ rsp + 0x48 ]
adcx r15, [ rsp + 0x40 ]
imul r9, [ rsi + 0x28 ], 0x2
xor rbp, rbp
adox rdi, [ rsp + 0x48 ]
adox r13, [ rsp + 0x40 ]
xchg rdx, r9
mulx rbp, r14, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r14
mulx r14, rbp, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r14
mov [ rsp + 0x80 ], rbp
mulx rbp, r14, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], rbp
mov [ rsp + 0x90 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
adcx r11, rax
adcx r10, rcx
xor rax, rax
adox r12, rbp
mov rcx, r14
adox rcx, r15
adcx r11, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x8 ]
xchg rdx, r8
mulx rax, r15, [ rsi + 0x10 ]
test al, al
adox rdi, rbp
adox r14, r13
mov r13, [ rsp + 0x30 ]
adcx r13, [ rsp + 0x38 ]
mov rbp, [ rsp + 0x28 ]
adcx rbp, [ rsp + 0x8 ]
mov [ rsp + 0x98 ], r10
xor r10, r10
adox rdi, r15
mov [ rsp + 0xa0 ], r11
mov r11, rax
adox r11, r14
adcx r12, r15
adcx rax, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r15, r9
xor rdx, rdx
adox r12, r15
mov r10, r14
adox r10, rax
adcx r13, [ rsp + 0x20 ]
adcx rbp, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], rbp
mulx rbp, rax, rdx
mov rdx, r8
mov [ rsp + 0xb0 ], r13
mulx r13, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r13
mov [ rsp + 0xc0 ], r8
mulx r8, r13, [ rsp + 0x0 ]
mov rdx, r13
mov [ rsp + 0xc8 ], r10
xor r10, r10
adox rdx, [ rsp + 0x60 ]
adox r8, [ rsp + 0x58 ]
adcx rdx, [ rsp + 0x80 ]
adcx r8, [ rsp + 0x78 ]
xor r13, r13
adox rdi, [ rsp - 0x8 ]
adox r11, [ rsp - 0x28 ]
adcx rdi, r15
adcx r14, r11
add rdx, [ rsp - 0x30 ]
adcx r8, [ rsp - 0x38 ]
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r15, r9
xor rdx, rdx
adox r10, r15
adox r11, r8
mov rdx, [ rsi + 0x8 ]
mulx r8, r13, [ rsp + 0x10 ]
mov rdx, r9
mulx r15, r9, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], r12
mov r12, r9
adcx r12, r9
mov [ rsp + 0xd8 ], rbp
mov rbp, r15
adcx rbp, r15
mov [ rsp + 0xe0 ], rax
mov rax, r13
test al, al
adox rax, [ rsp + 0x60 ]
adox r8, [ rsp + 0x58 ]
mov r13, r10
shrd r13, r11, 56
mov [ rsp + 0xe8 ], r13
mulx r13, r11, [ rsi + 0x10 ]
mov rdx, 0x38 
mov [ rsp + 0xf0 ], r8
bzhi r8, r10, rdx
mov rdx, rbx
mulx r10, rbx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], rax
mov [ rsp + 0x108 ], r13
mulx r13, rax, rcx
adox rdi, rbx
adox r10, r14
mov rdx, r8
mulx rcx, r8, [ rsi + 0x0 ]
test al, al
adox r12, [ rsp + 0x90 ]
adox rbp, [ rsp + 0x88 ]
adcx r9, [ rsp + 0x90 ]
adcx r15, [ rsp + 0x88 ]
xor rdx, rdx
adox r9, rax
mov r14, r13
adox r14, r15
adcx r9, r11
adcx r14, [ rsp + 0x108 ]
mov rbx, [ rsp + 0xd0 ]
add rbx, [ rsp + 0xe0 ]
mov r15, [ rsp + 0xc8 ]
adcx r15, [ rsp + 0xd8 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x110 ], r15
mov [ rsp + 0x118 ], rbx
mulx rbx, r15, [ rsi + 0x0 ]
mov [ rsp + 0x120 ], r14
xor r14, r14
adox r12, rax
adox r13, rbp
adcx rdi, r15
adcx rbx, r10
test al, al
adox r12, r11
adox r13, [ rsp + 0x108 ]
adcx r12, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mov r11, r8
test al, al
adox r11, [ rsp + 0x100 ]
adox rcx, [ rsp + 0xf0 ]
mov rax, r11
shrd rax, rcx, 56
xor r10, r10
adox rdi, rax
adox rbx, r10
mov r14, rdi
adcx r14, [ rsp + 0xe8 ]
adc rbx, 0x0
mov r8, r14
shrd r8, rbx, 56
mov rbp, rdx
mov rdx, [ rsp - 0x10 ]
mulx rcx, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r15
adox rcx, [ rsp + 0x120 ]
mov rdx, [ rsi + 0x10 ]
mulx rax, r10, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, rbp
mov rdx, [ rsi + 0x18 ]
mulx r15, rbp, rdx
mov rdx, rbp
adcx rdx, [ rsp + 0xb0 ]
adcx r15, [ rsp + 0xa8 ]
add rdx, r10
adcx rax, r15
test al, al
adox rdx, [ rsp + 0x70 ]
adox rax, [ rsp + 0x68 ]
adcx rdx, [ rsp - 0x18 ]
adcx rax, [ rsp - 0x20 ]
mov r10, [ rsp + 0x118 ]
mov rbp, r10
xor r15, r15
adox rbp, [ rsp + 0xe8 ]
mov [ rsp + 0x128 ], rax
mov rax, [ rsp + 0x110 ]
adox rax, r15
adcx r12, rdi
adcx rbx, r13
mov r10, rbp
shrd r10, rax, 56
xor r13, r13
adox r9, r10
adox rcx, r13
mov r15, 0xffffffffffffff 
mov rdi, r9
and rdi, r15
shrd r9, rcx, 56
add r12, [ rsp + 0xc0 ]
adcx rbx, [ rsp + 0xb8 ]
mov rax, [ rsp + 0x20 ]
mov r10, rax
xor rcx, rcx
adox r10, [ rsp + 0xa0 ]
mov r13, [ rsp + 0x18 ]
adox r13, [ rsp + 0x98 ]
adcx r12, r8
adc rbx, 0x0
mov rax, r12
and rax, r15
shrd r12, rbx, 56
xor r8, r8
adox rdx, r12
mov rcx, [ rsp + 0x128 ]
adox rcx, r8
mov rbx, rdx
shrd rbx, rcx, 56
add rbx, [ rsp + 0xf8 ]
and r14, r15
mov r12, rbx
shr r12, 56
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r8, rdx
xor rdx, rdx
adox r10, r8
adox r15, r13
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, [ rsp + 0x10 ]
lea r14, [ r14 + r12 ]
adcx r10, r13
adcx r8, r15
xor rdx, rdx
adox r10, r9
adox r8, rdx
mov r9, 0x38 
bzhi r15, r11, r9
mov r11, r10
shrd r11, r8, 56
bzhi r13, rbp, r9
lea r13, [ r13 + r12 ]
lea r11, [ r11 + r15 ]
bzhi rbp, r11, r9
shr r11, 56
lea r11, [ r11 + r14 ]
mov r12, r11
shr r12, 56
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rbp
mov r8, r13
shr r8, 56
lea r8, [ r8 + rdi ]
bzhi rdi, r13, r9
mov [ r14 + 0x0 ], rdi
mov [ r14 + 0x8 ], r8
lea r12, [ r12 + rax ]
mov [ r14 + 0x28 ], r12
bzhi rax, r11, r9
bzhi r15, r10, r9
bzhi r10, rcx, r9
mov [ r14 + 0x30 ], r10
mov [ r14 + 0x10 ], r15
bzhi rcx, rbx, r9
mov [ r14 + 0x20 ], rax
mov [ r14 + 0x38 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 432
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.0651
; seed 2842880071526023 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2288437 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=229, initial num_batches=31): 103414 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04518979548049608
; number reverted permutation / tried permutation: 67058 / 89487 =74.936%
; number reverted decision / tried decision: 62423 / 90512 =68.967%
; validated in 1.17s
