SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 376
mov rax, [ rsi + 0x28 ]
lea r10, [ 4 * rax]
imul rax, [ rsi + 0x40 ], 0x4
imul r11, [ rsi + 0x30 ], 0x2
mov rdx, 0x1 
shlx rcx, [ rsi + 0x28 ], rdx
imul r8, [ rsi + 0x18 ], 0x2
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r11
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x68 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rax
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x40 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, r11
imul rdx, [ rsi + 0x8 ], 0x2
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
imul rdx, [ rsi + 0x38 ], 0x4
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], rbp
mulx rbp, r12, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r14
mulx r14, r15, r8
mov rdx, rax
mov [ rsp + 0x30 ], r14
mulx r14, rax, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], rbx
mulx rbx, r13, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], rbx
mulx rbx, r8, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r8
mulx r8, rbx, rcx
test al, al
adox r12, rax
adox r14, rbp
mov rdx, [ rsi + 0x10 ]
mulx rax, rbp, rdx
adcx r12, rbp
adcx rax, r14
mov rdx, [ rsi + 0x20 ]
mulx rbp, r14, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r13
mulx r13, r10, rcx
imul rdx, [ rsi + 0x30 ], 0x4
mov [ rsp + 0x70 ], r13
mov [ rsp + 0x78 ], r10
mulx r10, r13, [ rsi + 0x28 ]
add r12, r9
adcx rax, [ rsp + 0x48 ]
test al, al
adox r13, [ rsp + 0x40 ]
adox r10, [ rsp + 0x28 ]
mov [ rsp + 0x80 ], rax
mulx rax, r9, [ rsi + 0x18 ]
adcx r14, r9
adcx rax, rbp
mulx r9, rbp, [ rsi + 0x20 ]
test al, al
adox r14, [ rsp + 0x20 ]
adox rax, [ rsp + 0x18 ]
mov rdx, r11
mov [ rsp + 0x88 ], r12
mulx r12, r11, [ rsi + 0x30 ]
mov rdx, rdi
mov [ rsp + 0x90 ], r10
mulx r10, rdi, [ rsi + 0x28 ]
adcx r11, rdi
adcx r10, r12
test al, al
adox r11, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r10
mulx r10, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], r11
mov [ rsp + 0xa8 ], r13
mulx r13, r11, r15
adcx r14, r11
adcx r13, rax
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, r12
xor rdx, rdx
adox r14, rdi
adox r10, r13
mov r12, r14
shrd r12, r10, 58
shr r10, 58
xor rdi, rdi
adox rbx, rbp
adox r9, r8
mov rdx, r15
mulx r8, r15, [ rsi + 0x10 ]
adcx rbx, rax
adcx r11, r9
xor rbp, rbp
adox rbx, r15
adox r8, r11
adcx rbx, [ rsp + 0x0 ]
adcx r8, [ rsp - 0x8 ]
test al, al
adox rbx, r12
adox r10, r8
mulx r13, rdi, [ rsi + 0x18 ]
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r12, rdx
imul rdx, [ rsi + 0x10 ], 0x2
mulx r11, r15, [ rsi + 0x0 ]
mov r8, rbx
shrd r8, r10, 58
shr r10, 58
mov [ rsp + 0xb0 ], r10
mov r10, rdi
mov [ rsp + 0xb8 ], r8
xor r8, r8
adox r10, [ rsp + 0xa8 ]
adox r13, [ rsp + 0x90 ]
adcx r10, r12
adcx r9, r13
mov rbp, [ rsi + 0x20 ]
lea rdi, [rbp + rbp]
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp + 0xa0 ]
adox r12, [ rsp + 0x98 ]
adcx r10, r15
adcx r11, r9
add r10, [ rsp + 0xb8 ]
adcx r11, [ rsp + 0xb0 ]
xor r15, r15
adox rdx, [ rsp + 0x38 ]
adox r12, [ rsp + 0x30 ]
mov r8, r10
shrd r8, r11, 58
shr r11, 58
mov r13, 0x3ffffffffffffff 
and rbx, r13
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, rdi
mov rdx, rdi
mulx r13, rdi, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], rbx
mov rbx, rdi
adox rbx, [ rsp + 0x88 ]
adox r13, [ rsp + 0x80 ]
adcx r9, r8
adcx r11, r12
mov r12, 0x3a 
bzhi r8, r10, r12
mov r10, rdx
mov rdx, [ rsp - 0x10 ]
mulx r12, rdi, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], r13
mov [ rsp + 0xd8 ], rbx
mulx rbx, r13, rax
adox rdi, r13
adox rbx, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, rdx
mov rdx, 0x3a 
mov [ rsp + 0xe0 ], r13
bzhi r13, r9, rdx
shrd r9, r11, 58
shr r11, 58
test al, al
adox rdi, [ rsp + 0x68 ]
adox rbx, [ rsp + 0x50 ]
adcx rdi, rbp
adcx r15, rbx
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x0 ]
xchg rdx, rax
mov [ rsp + 0xe8 ], r13
mulx r13, rbx, [ rsi + 0x38 ]
test al, al
adox rdi, rcx
adox rbp, r15
mov rdx, r9
adcx rdx, [ rsp + 0xd8 ]
adcx r11, [ rsp + 0xd0 ]
mov r9, 0x3a 
bzhi r15, rdx, r9
adox rbx, r12
adox r13, [ rsp + 0xe0 ]
shrd rdx, r11, 58
shr r11, 58
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, rcx, rdx
test al, al
adox rcx, [ rsp + 0x60 ]
adox r9, [ rsp + 0x58 ]
adcx rdi, r12
adcx r11, rbp
mov rdx, [ rsi + 0x40 ]
mulx r12, rbp, [ rsp - 0x18 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x20 ], r15
xchg rdx, r10
mulx r10, r15, [ rsi + 0x18 ]
mov [ rsp + 0xf0 ], r9
xor r9, r9
adox rbp, r15
adox r10, r12
adcx rbp, [ rsp + 0x78 ]
adcx r10, [ rsp + 0x70 ]
mulx r15, r12, [ rsi + 0x10 ]
add rbx, r12
adcx r15, r13
mov rdx, [ rsi + 0x8 ]
mulx r12, r13, rax
add rbx, r13
adcx r12, r15
xor rdx, rdx
adox rbx, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x0 ]
mulx rax, r9, r8
mov rdx, rdi
shrd rdx, r11, 58
shr r11, 58
xor r15, r15
adox rbx, rdx
adox r11, r12
mov r13, rbx
shrd r13, r11, 58
shr r11, 58
add rbp, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
add rcx, [ rsp - 0x20 ]
mov r12, [ rsp + 0xf0 ]
adcx r12, [ rsp - 0x28 ]
xor rdx, rdx
adox rbp, r9
adox rax, r10
adcx rbp, r13
adcx r11, rax
mov r15, rbp
shrd r15, r11, 58
shr r11, 58
mov rdx, [ rsp - 0x18 ]
mulx r13, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rax, r10, r8
test al, al
adox rcx, r10
adox rax, r12
mov rdx, 0x3a 
bzhi r8, r14, rdx
adox rcx, r9
adox r13, rax
xor r14, r14
adox rcx, r15
adox r11, r13
mov r12, rcx
shrd r12, r11, 57
shr r11, 57
xor r15, r15
adox r12, r8
adox r11, r15
mov r14, r12
shrd r14, r11, 58
bzhi r9, rbx, rdx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x30 ], r9
add r14, [ rsp + 0xc0 ]
mov r10, r14
shr r10, 58
bzhi rax, r14, rdx
mov [ rbx + 0x8 ], rax
bzhi r8, rdi, rdx
mov [ rbx + 0x28 ], r8
mov rdi, 0x1ffffffffffffff 
and rcx, rdi
bzhi r13, r12, rdx
mov [ rbx + 0x40 ], rcx
bzhi r12, rbp, rdx
mov [ rbx + 0x0 ], r13
mov rbp, [ rsp + 0xe8 ]
mov [ rbx + 0x18 ], rbp
mov [ rbx + 0x38 ], r12
add r10, [ rsp + 0xc8 ]
mov [ rbx + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 376
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4145
; seed 0995102962124495 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3159599 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=79, initial num_batches=31): 104598 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.033104833872906025
; number reverted permutation / tried permutation: 66101 / 89988 =73.455%
; number reverted decision / tried decision: 60458 / 90011 =67.167%
; validated in 1.974s
