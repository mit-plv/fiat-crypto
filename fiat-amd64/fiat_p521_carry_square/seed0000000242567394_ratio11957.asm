SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 416
mov rax, 0x1 
shlx r10, [ rsi + 0x28 ], rax
mov r11, [ rsi + 0x38 ]
mov rdx, r11
shl rdx, 0x2
mov r11, [ rsi + 0x20 ]
lea rcx, [r11 + r11]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rcx
mov rdx, rcx
mov [ rsp - 0x68 ], r13
mulx r13, rcx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], rdi
lea rdi, [ 4 * rdx]
imul rdx, [ rsi + 0x8 ], 0x2
xchg rdx, rdi
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r9
mulx r9, r15, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r8
imul r8, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x28 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r12
mulx r12, rcx, r8
mov rdx, r8
mov [ rsp - 0x10 ], r12
mulx r12, r8, [ rsi + 0x30 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], rbp
mulx rbp, rcx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rbp
mov rbp, [ rsi + 0x40 ]
mov [ rsp + 0x10 ], rcx
lea rcx, [ 4 * rbp]
imul rbp, [ rsi + 0x28 ], 0x4
mov [ rsp + 0x18 ], r12
mov r12, [ rsi + 0x38 ]
mov [ rsp + 0x20 ], r8
mov r8, r12
shl r8, 0x1
xchg rdx, rbp
mov [ rsp + 0x28 ], rdi
mulx rdi, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], rax
mulx rax, rbx, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], rax
mov [ rsp + 0x48 ], rbx
mulx rbx, rax, rbp
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], rax
mov [ rsp + 0x60 ], rbp
mulx rbp, rax, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], rax
mulx rax, rbp, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], rax
mov [ rsp + 0x80 ], rbp
mulx rbp, rax, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], rbp
mulx rbp, r8, rdx
xor rdx, rdx
adox r12, r15
adox r9, rdi
mov rdx, [ rsi + 0x38 ]
mulx rdi, r15, rbx
adcx r15, r8
adcx rbp, rdi
mov rdx, [ rsi + 0x30 ]
mulx rdi, r8, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x90 ], rax
mov [ rsp + 0x98 ], rbp
mulx rbp, rax, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], rbp
mulx rbp, r15, r10
mov rdx, rbx
mov [ rsp + 0xb0 ], rax
mulx rax, rbx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], r15
mulx r15, rbp, r11
xor rdx, rdx
adox r8, rbx
adox rax, rdi
mov rdx, r11
mulx rdi, r11, [ rsi + 0x10 ]
adcx r12, r11
adcx rdi, r9
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, rbx, r13
mov rdx, rbx
test al, al
adox rdx, [ rsp + 0xc8 ]
adox r11, [ rsp + 0xc0 ]
xchg rdx, rcx
mov [ rsp + 0xd0 ], rax
mulx rax, rbx, [ rsi + 0x8 ]
adcx r12, rbx
adcx rax, rdi
xor rdi, rdi
adox r12, [ rsp + 0x38 ]
adox rax, [ rsp + 0x30 ]
xchg rdx, r9
mulx rdi, rbx, [ rsi + 0x18 ]
adcx rcx, rbx
adcx rdi, r11
add rcx, [ rsp + 0xb8 ]
adcx rdi, [ rsp + 0x60 ]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r8
mulx r8, rbx, [ rsp + 0x28 ]
test al, al
adox rcx, rbx
adox r8, rdi
mov rdx, r12
shrd rdx, rax, 58
shr rax, 58
test al, al
adox rcx, rdx
adox rax, r8
mov rdx, r11
mulx rdi, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], rax
mov [ rsp + 0xe8 ], rcx
mulx rcx, rax, r13
mov rdx, r11
adcx rdx, [ rsp + 0x20 ]
adcx rdi, [ rsp + 0x18 ]
add rax, rbp
adcx r15, rcx
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, rbp, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], r14
mulx r14, rcx, r9
test al, al
adox rax, rbp
adox r11, r15
adcx rax, rbx
adcx r8, r11
imul rdx, [ rsi + 0x10 ], 0x2
mulx rbx, r9, [ rsi + 0x0 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], rbp
mulx rbp, r11, rdx
add rax, r9
adcx rbx, r8
mov rdx, [ rsi + 0x18 ]
lea r8, [rdx + rdx]
add r13, rcx
adcx r14, rdi
mov rdx, [ rsp + 0xf0 ]
mulx rcx, rdi, [ rsi + 0x18 ]
mov r9, [ rsp + 0xe0 ]
mov [ rsp + 0x100 ], rcx
mov rcx, [ rsp + 0xe8 ]
shrd rcx, r9, 58
shr r9, 58
mov [ rsp + 0x108 ], rdi
xor rdi, rdi
adox r13, r15
adox r14, [ rsp + 0xf8 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], rbp
mulx rbp, rdi, r8
adcx r13, rdi
adcx rbp, r14
test al, al
adox rax, rcx
adox r9, rbx
mov rdx, rax
shrd rdx, r9, 58
shr r9, 58
xor rbx, rbx
adox r13, rdx
adox r9, rbp
mov rcx, r13
shrd rcx, r9, 58
shr r9, 58
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, r8
mov rdx, r11
xor rbp, rbp
adox rdx, [ rsp + 0xd8 ]
mov rbx, [ rsp + 0x110 ]
adox rbx, [ rsp + 0xd0 ]
adcx rdx, r14
adcx rdi, rbx
xchg rdx, r10
mulx r14, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, r15
xor rdx, rdx
adox r10, [ rsp + 0x0 ]
adox rdi, [ rsp - 0x18 ]
adcx r10, rcx
adcx r9, rdi
mov r15, 0x3ffffffffffffff 
and rax, r15
mov rdx, r8
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x48 ]
adox rdx, [ rsp + 0x80 ]
mov rdi, [ rsp + 0x40 ]
adox rdi, [ rsp + 0x78 ]
adcx rdx, r8
adcx rcx, rdi
and r13, r15
mov r8, r10
shrd r8, r9, 58
shr r9, 58
xor rdi, rdi
adox rdx, rbx
adox rbp, rcx
adcx rdx, r11
adcx r14, rbp
xor r11, r11
adox rdx, r8
adox r9, r14
mov rdi, 0x1 
shlx rbx, [ rsi + 0x40 ], rdi
mov rcx, rdx
mov rdx, [ rsi + 0x40 ]
mulx rbp, r8, rbx
adcx r8, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x100 ]
xor rdx, rdx
adox r8, [ rsp + 0xb0 ]
adox rbp, [ rsp + 0xa8 ]
adcx r8, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
mov r11, [ rsp - 0x20 ]
mov r14, r11
test al, al
adox r14, [ rsp + 0xa0 ]
mov rdi, [ rsp - 0x28 ]
adox rdi, [ rsp + 0x98 ]
mov r11, rcx
and r11, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x118 ], r13
mulx r13, r15, rdx
adox r14, [ rsp - 0x30 ]
adox rdi, [ rsp - 0x38 ]
adcx r8, [ rsp + 0x90 ]
adcx rbp, [ rsp + 0x88 ]
xor rdx, rdx
adox r14, [ rsp - 0x8 ]
adox rdi, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
shrd rcx, r9, 58
shr r9, 58
test al, al
adox r14, rcx
adox r9, rdi
adcx r15, [ rsp + 0x58 ]
adcx r13, [ rsp + 0x50 ]
mov rdi, 0x3a 
bzhi rcx, r14, rdi
shrd r14, r9, 58
shr r9, 58
test al, al
adox r8, r14
adox r9, rbp
bzhi rbp, r8, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, r14, rbx
shrd r8, r9, 58
shr r9, 58
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], rbp
mov [ rdx + 0x28 ], r11
add r15, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x68 ]
xor rbx, rbx
adox r15, r14
adox rdi, r13
adcx r15, r8
adcx r9, rdi
mov r11, 0x1ffffffffffffff 
mov rbp, r15
and rbp, r11
mov r14, 0x3ffffffffffffff 
and r12, r14
shrd r15, r9, 57
shr r9, 57
xor r8, r8
adox r15, r12
adox r9, r8
mov rbx, r15
and rbx, r14
mov r13, [ rsp + 0xe8 ]
and r13, r14
shrd r15, r9, 58
lea r15, [ r15 + r13 ]
mov [ rdx + 0x30 ], rcx
mov rcx, r15
and rcx, r14
and r10, r14
mov [ rdx + 0x20 ], r10
shr r15, 58
lea r15, [ r15 + rax ]
mov [ rdx + 0x10 ], r15
mov rax, [ rsp + 0x118 ]
mov [ rdx + 0x18 ], rax
mov [ rdx + 0x8 ], rcx
mov [ rdx + 0x40 ], rbp
mov [ rdx + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 416
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1957
; seed 1344768553427739 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2621258 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=100, initial num_batches=31): 86636 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.033051305899686335
; number reverted permutation / tried permutation: 63266 / 89782 =70.466%
; number reverted decision / tried decision: 55605 / 90217 =61.635%
; validated in 1.392s
