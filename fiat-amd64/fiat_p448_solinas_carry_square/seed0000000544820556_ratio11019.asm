SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 352
mov rax, 0x1 
shlx r10, [ rsi + 0x28 ], rax
shlx r11, [ rsi + 0x20 ], rax
mov rdx, r10
mulx rcx, r10, [ rsi + 0x20 ]
shlx r8, [ rsi + 0x38 ], rax
imul r9, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, r9
mov [ rsp - 0x50 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r12
mulx r12, r9, r8
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r12
mulx r12, r11, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r15
mulx r15, rbp, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rbp
mulx rbp, r15, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r15
mulx r15, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rbx
mulx rbx, r14, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], rbx
mov [ rsp + 0x40 ], r14
mulx r14, rbx, r8
mov rdx, r11
add rdx, r11
mov [ rsp + 0x48 ], rax
mov rax, r12
adcx rax, r12
add r11, r10
mov [ rsp + 0x50 ], rax
mov rax, rcx
adcx rax, r12
mov r12, rbp
add r12, rbx
mov [ rsp + 0x58 ], rax
mov rax, r14
adcx rax, r15
mov [ rsp + 0x60 ], r11
mov r11, r12
add r11, rbp
adcx r15, rax
xor rbp, rbp
adox r11, rbx
adox r14, r15
imul rbx, [ rsi + 0x18 ], 0x2
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rbx
mulx rbx, rbp, rdx
add r11, rbp
mov rdx, rbx
adcx rdx, r14
xchg rdx, rdi
mov [ rsp + 0x70 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r14
mulx r14, rdi, rdx
xor rdx, rdx
adox r12, rbp
adox rbx, rax
adcx r12, [ rsp + 0x48 ]
adcx rbx, [ rsp + 0x30 ]
mov rax, rdi
test al, al
adox rax, rdi
mov rbp, r14
adox rbp, r14
adcx rdi, [ rsp + 0x28 ]
adcx r14, [ rsp + 0x0 ]
add rdi, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x8 ]
add r15, r10
adcx rcx, [ rsp + 0x50 ]
test al, al
adox rax, [ rsp + 0x28 ]
adox rbp, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r14
mulx r14, r10, r9
adcx rax, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
xor rdx, rdx
adox r12, r10
mov [ rsp + 0x90 ], rdi
mov rdi, r14
adox rdi, rbx
mov rbx, [ rsp + 0x60 ]
adcx rbx, [ rsp - 0x8 ]
mov [ rsp + 0x98 ], r13
mov r13, [ rsp + 0x58 ]
adcx r13, [ rsp - 0x10 ]
add r15, [ rsp - 0x8 ]
adcx rcx, [ rsp - 0x10 ]
test al, al
adox rbx, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
adcx r11, [ rsp + 0x48 ]
mov [ rsp + 0xa0 ], r13
mov r13, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x30 ]
mov [ rsp + 0xa8 ], rbx
xor rbx, rbx
adox r11, r10
adox r14, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], rdi
mulx rdi, rbx, rdx
adcx rax, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
xor rdx, rdx
adox rax, rbx
adox rdi, rbp
mov rdx, [ rsi + 0x28 ]
mulx rbp, rbx, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], rax
mulx rax, rdi, rdx
adcx r11, rdi
adcx rax, r14
mov rdx, r8
mulx r14, r8, [ rsi + 0x20 ]
add rbx, r8
adcx r14, rbp
add r15, [ rsp + 0x20 ]
adcx rcx, [ rsp + 0x18 ]
mov rbp, rbx
test al, al
adox rbp, r10
adox r13, r14
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rsp + 0x68 ]
adcx r15, rdi
adcx r8, rcx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, [ rsp + 0x68 ]
add rbx, [ rsp + 0x80 ]
adcx r14, [ rsp + 0x78 ]
add rbx, rcx
adcx rdi, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r12
mov [ rsp + 0xd0 ], r8
mulx r8, r12, r10
add rbp, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x38 ]
mov rdx, r9
mulx r10, r9, [ rsi + 0x8 ]
test al, al
adox rbp, r9
adox r10, r13
mov rdx, [ rsp + 0x68 ]
mulx r9, r13, [ rsi + 0x8 ]
adcx rbp, rcx
adcx r14, r10
mov rdx, 0x38 
bzhi rcx, rbp, rdx
bzhi r10, rbx, rdx
shrd rbp, r14, 56
add r11, r12
mov r14, r8
adcx r14, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r10
mulx r10, rax, [ rsp - 0x18 ]
add r11, r13
adcx r9, r14
mov rdx, [ rsp - 0x18 ]
mulx r14, r13, [ rsi + 0x8 ]
shrd rbx, rdi, 56
add r11, rax
adcx r10, r9
xor rdi, rdi
adox r15, r13
adox r14, [ rsp + 0xd0 ]
adcx r11, rbx
adc r10, 0x0
mov rax, rbp
test al, al
adox rax, r11
adox r10, rdi
mulx r13, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, rdx
mov rdx, r12
adcx rdx, [ rsp + 0xc8 ]
adcx r8, [ rsp + 0xb0 ]
mov r12, r9
add r12, [ rsp + 0xc0 ]
adcx r13, [ rsp + 0xb8 ]
add rdx, rbx
adcx r11, r8
mov r9, rax
shrd r9, r10, 56
test al, al
adox rbp, rdx
adox r11, rdi
mov rdx, [ rsi + 0x0 ]
mulx rbx, r10, [ rsp + 0x98 ]
adcx r15, r10
adcx rbx, r14
test al, al
adox r15, r9
adox rbx, rdi
mov rdx, 0x1 
shlx r14, [ rsi + 0x8 ], rdx
mov rdx, r14
mulx r8, r14, [ rsi + 0x0 ]
mov r9, r14
adcx r9, [ rsp + 0xa8 ]
adcx r8, [ rsp + 0xa0 ]
mov rdx, [ rsp + 0x98 ]
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, 0x38 
bzhi rdi, rbp, rdx
adox r12, r10
adox r14, r13
mov r13, r15
shrd r13, rbx, 56
add r12, [ rsp + 0x40 ]
adcx r14, [ rsp + 0x38 ]
shrd rbp, r11, 56
xor r11, r11
adox r12, r13
adox r14, r11
bzhi rbx, r12, rdx
shrd r12, r14, 56
add r9, rbp
adc r8, 0x0
lea r12, [ r12 + rcx ]
bzhi rcx, r12, rdx
shr r12, 56
mov r10, [ rsp + 0x90 ]
xor r13, r13
adox r10, [ rsp - 0x20 ]
mov r11, [ rsp + 0x88 ]
adox r11, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rbp, rdx
lea rdi, [ rdi + r12 ]
adcx r10, rbp
adcx r14, r11
add r10, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
mov rdx, 0x38 
bzhi r11, rax, rdx
lea r11, [ r11 + r12 ]
mov rax, r9
shrd rax, r8, 56
mov r8, rdi
shr r8, 56
add r10, rax
adc r14, 0x0
mov r12, r10
shrd r12, r14, 56
add r12, [ rsp + 0xd8 ]
bzhi rbp, r10, rdx
mov rax, r12
shr rax, 56
lea rax, [ rax + r11 ]
bzhi r11, rax, rdx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x20 ], r11
mov [ r10 + 0x10 ], rbp
bzhi r14, rdi, rdx
bzhi rdi, r12, rdx
mov [ r10 + 0x18 ], rdi
shr rax, 56
bzhi r12, r15, rdx
lea rax, [ rax + r12 ]
bzhi r15, r9, rdx
mov [ r10 + 0x28 ], rax
mov [ r10 + 0x38 ], rcx
lea r8, [ r8 + r15 ]
mov [ r10 + 0x8 ], r8
mov [ r10 + 0x30 ], rbx
mov [ r10 + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 352
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1019
; seed 3631009102549824 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3516848 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=112, initial num_batches=31): 113250 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03220213099912194
; number reverted permutation / tried permutation: 66294 / 90102 =73.577%
; number reverted decision / tried decision: 61579 / 89897 =68.500%
; validated in 1.922s
