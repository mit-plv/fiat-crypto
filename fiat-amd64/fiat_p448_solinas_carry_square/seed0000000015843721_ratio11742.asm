SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 392
mov rax, [ rsi + 0x38 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x38 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x28 ]
lea r9, [rdx + rdx]
mov rdx, r10
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, 0x1 
mov [ rsp - 0x70 ], r12
shlx r12, [ rsi + 0x30 ], rbp
imul rbp, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rdi
mulx rdi, rbp, r12
mov rdx, r12
mov [ rsp - 0x30 ], r8
mulx r8, r12, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], rcx
mulx rcx, r12, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rcx
mov [ rsp - 0x8 ], r12
mulx r12, rcx, r8
mov rdx, r13
mov [ rsp + 0x0 ], r12
mulx r12, r13, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r12
mulx r12, rcx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], r10
mulx r10, rbx, r9
test al, al
adox rbp, rcx
adox r12, rdi
mov rdx, rax
adcx rdx, rax
mov rdi, r11
adcx rdi, r11
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r12
mov [ rsp + 0x38 ], rbp
mulx rbp, r12, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], r12
mulx r12, rbp, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x50 ], r15
mulx r15, r8, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], r10
mulx r10, r14, rdx
test al, al
adox rax, r14
mov rdx, r10
adox rdx, r11
adcx rax, rbp
mov r11, r12
adcx r11, rdx
xor rdx, rdx
adox rcx, r14
adox r10, rdi
adcx rcx, rbp
adcx r12, r10
mov rdi, r8
test al, al
adox rdi, r8
mov rbp, r15
adox rbp, r15
adcx rdi, rbx
adcx rbp, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x20 ]
mulx r10, r14, rdx
mov rdx, r13
mov [ rsp + 0x68 ], r10
mulx r10, r13, [ rsi + 0x18 ]
add rdi, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x50 ]
mov [ rsp + 0x70 ], r14
xor r14, r14
adox r8, rbx
adox r15, [ rsp + 0x60 ]
mulx r14, rbx, [ rsi + 0x28 ]
adcx rax, r13
mov rdx, r10
adcx rdx, r11
xor r11, r11
adox rdi, [ rsp + 0x28 ]
adox rbp, [ rsp + 0x20 ]
mov [ rsp + 0x78 ], rdx
mov rdx, rbx
adcx rdx, [ rsp - 0x18 ]
mov [ rsp + 0x80 ], rax
mov rax, r14
adcx rax, [ rsp - 0x30 ]
mov [ rsp + 0x88 ], rbp
xor rbp, rbp
adox rcx, r13
adox r10, r12
mov r11, rdx
adcx r11, [ rsp - 0x18 ]
mov r12, rax
adcx r12, [ rsp - 0x30 ]
xor r13, r13
adox r11, rbx
adox r14, r12
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, [ rsp - 0x48 ]
adcx r11, [ rsp + 0x70 ]
adcx r14, [ rsp + 0x68 ]
test al, al
adox r11, [ rsp - 0x38 ]
adox r14, [ rsp - 0x40 ]
mov rdx, 0x1 
shlx r13, [ rsi + 0x18 ], rdx
adcx r8, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x50 ]
mov rdx, r13
mov [ rsp + 0x90 ], r10
mulx r10, r13, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rcx
mov rcx, rbx
mov [ rsp + 0xa0 ], r15
xor r15, r15
adox rcx, [ rsp + 0x38 ]
adox r12, [ rsp + 0x30 ]
adcx rcx, r13
adcx r10, r12
mov rbx, rcx
shrd rbx, r10, 56
mulx r12, r13, [ rsi + 0x10 ]
xor r10, r10
adox rdi, r13
adox r12, [ rsp + 0x88 ]
adcx rbp, [ rsp + 0x70 ]
adcx rax, [ rsp + 0x68 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, r13, rdx
test al, al
adox rbp, [ rsp - 0x38 ]
adox rax, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
add r8, [ rsp + 0x28 ]
mov rdx, [ rsp + 0x20 ]
adcx rdx, [ rsp + 0xa0 ]
mov [ rsp + 0xa8 ], rdx
imul rdx, [ rsi + 0x20 ], 0x2
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], rbx
mulx rbx, r8, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r12
mov r12, r8
test al, al
adox r12, [ rsp + 0x38 ]
adox rbx, [ rsp + 0x30 ]
mov [ rsp + 0xc8 ], rdi
mulx rdi, r8, [ rsi + 0x10 ]
adcx r11, r13
adcx r10, r14
add r11, [ rsp - 0x8 ]
adcx r10, [ rsp - 0x10 ]
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], rdi
mulx rdi, r14, r15
mov rdx, 0x38 
bzhi r15, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r15
mulx r15, rcx, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r8
mov [ rsp + 0xe8 ], r10
mulx r10, r8, r9
adox r12, rcx
adox r15, rbx
add r12, [ rsp + 0x48 ]
adcx r15, [ rsp + 0x40 ]
add rbp, [ rsp - 0x20 ]
adcx rax, [ rsp - 0x28 ]
add r12, [ rsp + 0x18 ]
adcx r15, [ rsp + 0x10 ]
add rbp, [ rsp - 0x8 ]
adcx rax, [ rsp - 0x10 ]
mov rdx, 0x38 
bzhi rbx, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], rbx
mulx rbx, rcx, r13
adox r11, r14
adox rdi, [ rsp + 0xe8 ]
mov rdx, r13
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, r13
mov [ rsp + 0xf8 ], rax
xor rax, rax
adox rdx, [ rsp + 0xc8 ]
adox r14, [ rsp + 0xc0 ]
adcx r11, rcx
adcx rbx, rdi
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, rdi, rdx
shrd r12, r15, 56
xor rdx, rdx
adox r11, [ rsp + 0xb8 ]
adox rbx, rdx
mov rax, rdi
adcx rax, [ rsp + 0x80 ]
adcx r13, [ rsp + 0x78 ]
mov r15, r12
add r15, r11
adc rbx, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r11, rdi, rdx
mov rdx, 0x38 
mov [ rsp + 0x100 ], r13
bzhi r13, r15, rdx
shrd r15, rbx, 56
add rcx, r8
adcx r10, r14
add rcx, r15
adc r10, 0x0
mov r8, rdi
xor r14, r14
adox r8, [ rsp + 0x98 ]
adox r11, [ rsp + 0x90 ]
adcx r8, [ rsp + 0xe0 ]
adcx r11, [ rsp + 0xd0 ]
bzhi rbx, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, rdi, rdx
adox rbp, rdi
adox r15, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x8 ]
lea rdi, [rdx + rdx]
test al, al
adox r12, rbp
adox r15, r14
mov rdx, rdi
mulx rbp, rdi, [ rsi + 0x0 ]
mov rdx, r9
mulx r14, r9, [ rsi + 0x8 ]
adcx r8, r9
adcx r14, r11
xor rdx, rdx
adox r8, [ rsp + 0x8 ]
adox r14, [ rsp + 0x0 ]
shrd rcx, r10, 56
test al, al
adox r8, rcx
adox r14, rdx
mov r10, r8
shrd r10, r14, 56
mov rdx, [ rsi + 0x0 ]
mulx r9, r11, [ rsp - 0x48 ]
add r10, [ rsp + 0xf0 ]
mov rdx, rdi
add rdx, [ rsp + 0xb0 ]
adcx rbp, [ rsp + 0xa8 ]
mov rdi, 0x38 
bzhi rcx, r10, rdi
mov r14, r12
shrd r14, r15, 56
add rdx, r14
adc rbp, 0x0
shr r10, 56
lea r13, [ r13 + r10 ]
bzhi r15, rdx, rdi
adox rax, r11
adox r9, [ rsp + 0x100 ]
shrd rdx, rbp, 56
bzhi r11, r8, rdi
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x30 ], r11
adox rax, rdx
mov r14, 0x0 
adox r9, r14
bzhi rbp, rax, rdi
mov [ r8 + 0x10 ], rbp
shrd rax, r9, 56
bzhi rdx, r12, rdi
lea rdx, [ rdx + r10 ]
add rax, [ rsp + 0xd8 ]
bzhi r12, rax, rdi
bzhi r10, rdx, rdi
shr rax, 56
lea rax, [ rax + r13 ]
bzhi r13, rax, rdi
mov [ r8 + 0x20 ], r13
mov [ r8 + 0x0 ], r10
mov [ r8 + 0x18 ], r12
shr rdx, 56
lea rdx, [ rdx + r15 ]
shr rax, 56
mov [ r8 + 0x8 ], rdx
lea rax, [ rax + rbx ]
mov [ r8 + 0x38 ], rcx
mov [ r8 + 0x28 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 392
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.1742
; seed 2911632409712484 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4676587 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=191, initial num_batches=31): 186453 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03986946035645226
; number reverted permutation / tried permutation: 66284 / 90081 =73.583%
; number reverted decision / tried decision: 60329 / 89918 =67.093%
; validated in 2.404s
