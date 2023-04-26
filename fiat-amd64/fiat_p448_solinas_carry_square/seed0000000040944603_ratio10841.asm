SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 400
mov rax, [ rsi + 0x30 ]
mov r10, rax
shl r10, 0x1
mov rax, [ rsi + 0x38 ]
mov r11, rax
shl r11, 0x1
mov rdx, [ rsi + 0x30 ]
mulx rcx, rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r9, r8, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
shl rbx, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r14
mulx r14, r15, rdx
mov rdx, r8
add rdx, r8
mov [ rsp - 0x30 ], r14
mov r14, r9
adcx r14, r9
mov [ rsp - 0x28 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r14
mulx r14, r13, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r13
mulx r13, r14, r11
mov rdx, r11
mov [ rsp + 0x0 ], r13
mulx r13, r11, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r14
mov r14, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r15
lea r15, [r14 + r14]
mov [ rsp + 0x18 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r14
mulx r14, r15, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r14
mov [ rsp + 0x38 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r15
mov [ rsp + 0x48 ], r14
mulx r14, r15, [ rsi + 0x28 ]
mov rdx, rax
test al, al
adox rdx, r15
mov [ rsp + 0x50 ], rbx
mov rbx, r14
adox rbx, rcx
mov [ rsp + 0x58 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], rbp
mulx rbp, r12, rdx
mov rdx, rdi
adcx rdx, rax
adcx rcx, rbx
test al, al
adox rdx, r15
adox r14, rcx
adcx rdi, r12
mov rax, rbp
adcx rax, rbx
xor r15, r15
adox rdx, r12
adox rbp, r14
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mulx rcx, r12, r10
mov rdx, [ rsi + 0x0 ]
mulx r15, r14, r10
adcx r12, r11
adcx r13, rcx
imul rdx, [ rsi + 0x28 ], 0x2
mulx rcx, r11, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r15
mov [ rsp + 0x78 ], r14
mulx r14, r15, [ rsi + 0x18 ]
add rbx, r15
mov [ rsp + 0x80 ], rcx
mov rcx, r14
adcx rcx, rbp
test al, al
adox rdi, r15
adox r14, rax
adcx rbx, [ rsp + 0x68 ]
adcx rcx, [ rsp + 0x60 ]
mulx rbp, rax, [ rsi + 0x20 ]
xor r15, r15
adox r8, rax
mov [ rsp + 0x88 ], r11
mov r11, rbp
adox r11, r9
adcx r8, [ rsp + 0x58 ]
adcx r11, [ rsp + 0x50 ]
mov r9, rax
add r9, [ rsp + 0x10 ]
adcx rbp, [ rsp - 0x18 ]
mulx r15, rax, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], r15
xor r15, r15
adox rbx, [ rsp - 0x20 ]
adox rcx, [ rsp - 0x38 ]
mov r15, 0x1 
mov [ rsp + 0x98 ], rax
shlx rax, [ rsi + 0x10 ], r15
adcx rdi, [ rsp + 0x68 ]
adcx r14, [ rsp + 0x60 ]
add r9, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x50 ]
xchg rdx, rax
mov [ rsp + 0xa0 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rbx
mov rbx, r12
add rbx, r15
adcx rcx, r13
add rdi, [ rsp + 0x8 ]
adcx r14, [ rsp + 0x0 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb0 ], r14
mov [ rsp + 0xb8 ], rdi
mulx rdi, r14, [ rsp - 0x40 ]
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0xc0 ], rcx
mov [ rsp + 0xc8 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], rbx
xor rbx, rbx
adox r9, [ rsp + 0x28 ]
adox rbp, [ rsp + 0x20 ]
adcx r9, r14
adcx rdi, rbp
xor r14, r14
adox r8, [ rsp + 0x28 ]
adox r11, [ rsp + 0x20 ]
mulx rbp, rbx, [ rsi + 0x18 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r11
mov [ rsp + 0xe0 ], r8
mulx r8, r11, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe8 ], r8
mulx r8, r15, rax
adcx r12, rbx
adcx rbp, r13
add r12, r15
adcx r8, rbp
mov rdx, r10
mulx r13, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mulx rbx, rax, rdx
xor rdx, rdx
adox r9, rcx
adox rdi, [ rsp + 0xd0 ]
adcx r12, r10
adcx r13, r8
add r12, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x30 ]
mov rcx, rax
add rcx, rax
mov r15, rbx
adcx r15, rbx
mov rbp, r12
shrd rbp, r13, 56
test al, al
adox rax, [ rsp - 0x28 ]
adox rbx, [ rsp - 0x30 ]
adcx rax, [ rsp - 0x8 ]
adcx rbx, [ rsp - 0x10 ]
mov r8, 0x38 
bzhi r10, r12, r8
adox rax, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r10
mulx r10, r8, [ rsp - 0x40 ]
add rcx, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x30 ]
mov rdx, r8
test al, al
adox rdx, [ rsp + 0xc8 ]
adox r10, [ rsp + 0xc0 ]
adcx rcx, [ rsp - 0x8 ]
adcx r15, [ rsp - 0x10 ]
mov r8, [ rsp + 0x8 ]
mov [ rsp + 0xf8 ], r11
mov r11, r8
add r11, [ rsp + 0xa8 ]
mov [ rsp + 0x100 ], rdi
mov rdi, [ rsp + 0x0 ]
adcx rdi, [ rsp + 0xa0 ]
add rax, r12
adcx r13, rbx
mov r8, 0x38 
bzhi rbx, rdx, r8
mov r12, rdx
mov rdx, [ rsp - 0x40 ]
mov [ rsp + 0x108 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
adox r11, r8
adox rbx, rdi
mov rdx, [ rsi + 0x0 ]
mulx r8, rdi, r14
xor rdx, rdx
adox r11, rdi
adox r8, rbx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbx, rdx
mov rdx, rbx
adcx rdx, [ rsp + 0xb8 ]
adcx rdi, [ rsp + 0xb0 ]
mov rbx, rbp
add rbx, rdx
adc rdi, 0x0
shrd r12, r10, 56
mov r10, rbx
shrd r10, rdi, 56
test al, al
adox r11, r12
mov rdx, 0x0 
adox r8, rdx
mov rdx, [ rsp + 0x18 ]
mulx r12, rdi, [ rsi + 0x0 ]
adcx rbp, r11
adc r8, 0x0
mov rdx, rbp
shrd rdx, r8, 56
mov r11, rdi
test al, al
adox r11, [ rsp + 0xe0 ]
adox r12, [ rsp + 0xd8 ]
adcx r11, r10
adc r12, 0x0
mov r10, r11
shrd r10, r12, 56
mov rdi, 0xffffffffffffff 
and r11, rdi
adox rcx, [ rsp + 0x48 ]
adox r15, [ rsp + 0x40 ]
and rbx, rdi
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r12, rdx
adox rcx, r12
adox rdi, r15
mov rdx, [ rsi + 0x10 ]
mulx r12, r15, r14
adcx rcx, r15
adcx r12, rdi
test al, al
adox rcx, [ rsp + 0x98 ]
adox r12, [ rsp + 0x90 ]
adcx r9, [ rsp + 0x88 ]
mov rdx, [ rsp + 0x80 ]
adcx rdx, [ rsp + 0x100 ]
test al, al
adox r9, r8
mov r14, 0x0 
adox rdx, r14
mov r8, r9
shrd r8, rdx, 56
add rcx, [ rsp + 0x78 ]
adcx r12, [ rsp + 0x70 ]
mov rdi, 0x38 
bzhi r15, r9, rdi
adox rcx, r8
adox r12, r14
xor r9, r9
adox rax, [ rsp + 0xf8 ]
adox r13, [ rsp + 0xe8 ]
bzhi r14, rcx, rdi
adox rax, r10
adox r13, r9
mov r10, rax
shrd r10, r13, 56
add r10, [ rsp + 0x108 ]
shrd rcx, r12, 56
add rcx, [ rsp + 0xf0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], r14
mov r8, rcx
shr r8, 56
lea rbx, [ rbx + r8 ]
bzhi r12, rbx, rdi
shr rbx, 56
mov r14, r10
shr r14, 56
bzhi r13, rcx, rdi
bzhi rcx, rbp, rdi
lea rcx, [ rcx + r8 ]
lea rbx, [ rbx + r11 ]
lea r14, [ r14 + rcx ]
mov [ rdx + 0x8 ], rbx
mov rbp, r14
shr rbp, 56
lea rbp, [ rbp + r15 ]
bzhi r11, rax, rdi
mov [ rdx + 0x28 ], rbp
mov [ rdx + 0x10 ], r11
mov [ rdx + 0x38 ], r13
bzhi r15, r10, rdi
bzhi rax, r14, rdi
mov [ rdx + 0x18 ], r15
mov [ rdx + 0x20 ], rax
mov [ rdx + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 400
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0841
; seed 0274475631531383 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4725278 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=203, initial num_batches=31): 192769 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04079527172792796
; number reverted permutation / tried permutation: 66356 / 90417 =73.389%
; number reverted decision / tried decision: 60065 / 89582 =67.050%
; validated in 2.573s
