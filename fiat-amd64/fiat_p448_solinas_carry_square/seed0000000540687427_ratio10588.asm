SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 400
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x30 ]
lea rdx, [r11 + r11]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rdx
mov rdx, 0x1 
shlx r9, [ rsi + 0x18 ], rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
imul rdx, [ rsi + 0x20 ], 0x2
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
imul rdx, [ rsi + 0x28 ], 0x2
mov [ rsp - 0x58 ], r15
imul r15, [ rsi + 0x8 ], 0x2
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rcx
mov rcx, 0x1 
mov [ rsp - 0x28 ], r8
shlx r8, [ rsi + 0x10 ], rcx
mov [ rsp - 0x20 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r8
mov r8, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], rcx
lea rcx, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], rbx
mulx rbx, rbp, rcx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rdi
mulx rdi, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r14
mulx r14, r13, rcx
mov rdx, r12
test al, al
adox rdx, rbp
mov [ rsp + 0x38 ], r14
mov r14, rbx
adox r14, rdi
mov [ rsp + 0x40 ], r13
mov r13, rdx
adcx r13, r12
adcx rdi, r14
xchg rdx, r15
mov [ rsp + 0x48 ], r9
mulx r9, r12, [ rsi + 0x0 ]
mov rdx, rcx
mov [ rsp + 0x50 ], r9
mulx r9, rcx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], rcx
mulx rcx, r9, rdx
xor rdx, rdx
adox r13, rbp
adox rbx, rdi
adcx r13, rax
mov rbp, r10
adcx rbp, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, [ rsp + 0x48 ]
mov rdx, r9
test al, al
adox rdx, r9
mov [ rsp + 0x70 ], rbx
mov rbx, rcx
adox rbx, rcx
adcx r9, [ rsp + 0x20 ]
adcx rcx, [ rsp + 0x18 ]
test al, al
adox r15, rax
adox r10, r14
adcx r13, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
test al, al
adox r15, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], rdi
mulx rdi, r14, r11
mov rdx, r11
mov [ rsp + 0x80 ], rdi
mulx rdi, r11, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r11
mulx r11, rdi, [ rsi + 0x10 ]
adcx r15, rdi
mov [ rsp + 0x98 ], r14
mov r14, r11
adcx r14, r10
xor r10, r10
adox r13, rdi
adox r11, rbp
adcx r15, [ rsp + 0x40 ]
adcx r14, [ rsp + 0x38 ]
test al, al
adox rax, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x18 ]
adcx rax, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x8 ]
add r15, [ rsp - 0x38 ]
adcx r14, [ rsp - 0x40 ]
add rax, [ rsp + 0x68 ]
adcx rbx, [ rsp + 0x60 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, rdi, rdx
xor rdx, rdx
adox r9, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r14
mov [ rsp + 0xa8 ], r15
mulx r15, r14, rbp
adcx rax, rdi
adcx r10, rbx
mov rdx, [ rsi + 0x20 ]
mulx rdi, rbx, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], rax
mulx rax, r10, [ rsp - 0x48 ]
test al, al
adox r9, [ rsp + 0x68 ]
adox rcx, [ rsp + 0x60 ]
adcx r14, rbx
adcx rdi, r15
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rsp + 0x48 ]
mov rdx, r14
add rdx, r10
adcx rax, rdi
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], rcx
mov [ rsp + 0xc8 ], r9
mulx r9, rcx, [ rsp - 0x20 ]
xor rdx, rdx
adox r14, rcx
adox r9, rdi
mov rdx, [ rsi + 0x10 ]
mulx rcx, rdi, rdx
mov rdx, r8
mov [ rsp + 0xd0 ], r11
mulx r11, r8, [ rsi + 0x10 ]
adcx r14, r15
adcx rbx, r9
xor rdx, rdx
adox r10, r8
adox r11, rax
adcx r13, rdi
adcx rcx, [ rsp + 0xd0 ]
mov r15, r14
shrd r15, rbx, 56
mov rdx, r12
mulx rax, r12, [ rsi + 0x30 ]
mov r9, r12
test al, al
adox r9, r12
mov rdi, rax
adox rdi, rax
adcx r13, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x38 ]
add r9, [ rsp - 0x28 ]
adcx rdi, [ rsp - 0x30 ]
xor r8, r8
adox r13, [ rsp + 0x78 ]
adox rcx, [ rsp + 0x70 ]
mulx r8, rbx, [ rsi + 0x0 ]
adcx r9, [ rsp + 0x98 ]
adcx rdi, [ rsp + 0x80 ]
mov [ rsp + 0xd8 ], r15
mov r15, 0x38 
mov [ rsp + 0xe0 ], rcx
bzhi rcx, r14, r15
mulx r15, r14, [ rsi + 0x10 ]
adox r12, [ rsp - 0x28 ]
adox rax, [ rsp - 0x30 ]
xor rdx, rdx
adox r12, [ rsp + 0x98 ]
adox rax, [ rsp + 0x80 ]
adcx r10, [ rsp + 0x90 ]
adcx r11, [ rsp + 0x88 ]
mov [ rsp + 0xe8 ], rcx
xor rcx, rcx
adox r10, rbx
adox r8, r11
adcx r9, r14
mov rdx, r15
adcx rdx, rdi
mov rbx, r10
shrd rbx, r8, 56
xor rdi, rdi
adox r12, r14
adox r15, rax
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r14, [ rsp + 0x48 ]
adcx r9, r14
adcx rax, rcx
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ rsp - 0x48 ]
test al, al
adox r13, r11
adox r8, [ rsp + 0xe0 ]
adcx r13, [ rsp + 0xd8 ]
adc r8, 0x0
mov rdx, [ rsp - 0x20 ]
mulx r14, rcx, [ rsi + 0x0 ]
mov rdx, rbx
add rdx, r13
adc r8, 0x0
mov r11, rdx
shrd r11, r8, 56
add rbx, [ rsp + 0xa8 ]
mov r13, [ rsp + 0xa0 ]
adc r13, 0x0
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r14
mulx r14, rdi, rdx
add r12, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x50 ]
mov rdx, rbx
shrd rdx, r13, 56
mov r13, rdi
add r13, [ rsp + 0xc8 ]
adcx r14, [ rsp + 0xc0 ]
xor rdi, rdi
adox r12, rdx
adox r15, rdi
mov rdx, 0xffffffffffffff 
mov rdi, r12
and rdi, rdx
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0xf8 ], rdi
mov [ rsp + 0x100 ], r14
mulx r14, rdi, [ rsi + 0x10 ]
shrd r12, r15, 56
mov [ rsp + 0x108 ], r12
mulx r12, r15, [ rsi + 0x8 ]
test al, al
adox r9, r15
adox r12, rax
mov rdx, rdi
adcx rdx, [ rsp + 0xb8 ]
adcx r14, [ rsp + 0xb0 ]
xor rax, rax
adox r9, [ rsp - 0x10 ]
adox r12, [ rsp - 0x18 ]
adcx r9, r11
adc r12, 0x0
mov r11, r9
shrd r11, r12, 56
xor rdi, rdi
adox rdx, [ rsp + 0x30 ]
adox r14, [ rsp + 0x28 ]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r15, rbp
adcx rax, r15
adcx r12, r14
test al, al
adox rax, r11
adox r12, rdi
mov rdx, rax
shrd rdx, r12, 56
mov rbp, 0x38 
bzhi r11, r10, rbp
lea rdx, [ rdx + r11 ]
mov r10, rdx
shr r10, 56
bzhi r14, rax, rbp
bzhi r15, rdx, rbp
adox r13, rcx
mov rax, [ rsp + 0xf0 ]
adox rax, [ rsp + 0x100 ]
bzhi rcx, r8, rbp
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x38 ], r15
adox r13, [ rsp + 0x108 ]
adox rax, rdi
mov r12, r13
shrd r12, rax, 56
bzhi r11, rbx, rbp
lea r11, [ r11 + r10 ]
bzhi rbx, r11, rbp
add r12, [ rsp + 0xe8 ]
mov rdx, r12
shr rdx, 56
bzhi r15, r13, rbp
lea rcx, [ rcx + r10 ]
lea rdx, [ rdx + rcx ]
bzhi r10, r12, rbp
mov [ r8 + 0x18 ], r10
mov [ r8 + 0x10 ], r15
bzhi r13, r9, rbp
mov r9, rdx
shr r9, 56
bzhi rax, rdx, rbp
mov [ r8 + 0x20 ], rax
lea r9, [ r9 + r13 ]
shr r11, 56
add r11, [ rsp + 0xf8 ]
mov [ r8 + 0x0 ], rbx
mov [ r8 + 0x30 ], r14
mov [ r8 + 0x8 ], r11
mov [ r8 + 0x28 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 400
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0588
; seed 2239809887577443 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3505755 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=113, initial num_batches=31): 115093 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03282973282502628
; number reverted permutation / tried permutation: 65759 / 90235 =72.875%
; number reverted decision / tried decision: 60680 / 89764 =67.599%
; validated in 1.712s
