SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 344
mov rax, [ rsi + 0x10 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x38 ]
mov r9, rdx
shl r9, 0x2
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r9
mov rdx, 0x2 
mov [ rsp - 0x60 ], r14
shlx r14, [ rsi + 0x28 ], rdx
mov [ rsp - 0x58 ], r15
imul r15, [ rsi + 0x20 ], 0x2
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, r14
imul rdx, [ rsi + 0x40 ], 0x4
mov [ rsp - 0x40 ], r12
mulx r12, r14, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r14
mulx r14, r12, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], r10
mov r10, 0x1 
mov [ rsp - 0x20 ], r8
shlx r8, [ rsi + 0x30 ], r10
mov [ rsp - 0x18 ], r8
mulx r8, r10, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rcx
mov rcx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], rbp
lea rbp, [rcx + rcx]
mov rcx, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], rbp
mov rbp, rcx
shl rbp, 0x2
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r8
mulx r8, rbx, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r10
mov [ rsp + 0x20 ], r15
mulx r15, r10, rbp
mov rdx, rbp
mov [ rsp + 0x28 ], r15
mulx r15, rbp, [ rsi + 0x18 ]
xor rdx, rdx
adox rdi, rbp
adox r15, r13
adcx r12, rax
adcx r11, r14
mov rdx, [ rsi + 0x20 ]
mulx r13, rax, r9
mov rdx, 0x1 
shlx r14, [ rsi + 0x28 ], rdx
mov rdx, r14
mulx rbp, r14, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], r15
xor r15, r15
adox rbx, rax
adox r13, r8
adcx r14, r10
adcx rbp, [ rsp + 0x28 ]
mov r8, rdx
mov rdx, [ rsp + 0x20 ]
mulx rax, r10, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r13
xor r13, r13
adox r12, r10
adox rax, r11
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, r9
adcx r14, r10
adcx r13, rbp
mov rdx, [ rsi + 0x10 ]
mulx r10, rbp, r9
add rdi, rbp
adcx r10, [ rsp + 0x30 ]
test al, al
adox rdi, [ rsp + 0x18 ]
adox r10, [ rsp + 0x10 ]
adcx rdi, [ rsp + 0x8 ]
adcx r10, [ rsp - 0x8 ]
mov rdx, rdi
shrd rdx, r10, 58
shr r10, 58
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], rax
mulx rax, r15, rcx
xor rdx, rdx
adox r14, r15
adox rax, r13
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, [ rsp + 0x0 ]
adcx r14, r13
adcx r15, rax
test al, al
adox r14, rbp
adox r10, r15
mov rdx, [ rsi + 0x28 ]
mulx rax, rbp, rcx
mov rdx, r9
mulx r13, r9, [ rsi + 0x30 ]
adcx r9, rbp
adcx rax, r13
mov rdx, r8
mulx r15, r8, [ rsi + 0x8 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], rax
mulx rax, r13, rcx
xor rdx, rdx
adox rbx, r13
adox rax, [ rsp + 0x38 ]
adcx rbx, [ rsp - 0x10 ]
adcx rax, [ rsp - 0x20 ]
mov rdx, rcx
mulx r13, rcx, [ rsi + 0x20 ]
test al, al
adox r12, r8
adox r15, [ rsp + 0x50 ]
mov rdx, [ rsp - 0x28 ]
mov [ rsp + 0x60 ], r15
mulx r15, r8, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r12
mov r12, 0x3ffffffffffffff 
mov [ rsp + 0x70 ], r13
mov r13, r14
and r13, r12
and rdi, r12
shrd r14, r10, 58
shr r10, 58
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r13
mov [ rsp + 0x80 ], rdi
mulx rdi, r13, rdx
xor rdx, rdx
adox r9, r13
adox rdi, [ rsp + 0x58 ]
adcx rbx, r8
adcx r15, rax
imul rax, [ rsi + 0x18 ], 0x2
mov rdx, [ rsi + 0x8 ]
mulx r13, r8, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r9
mulx r9, rdi, rax
test al, al
adox rbx, r14
adox r10, r15
mov rdx, [ rsi + 0x38 ]
lea r14, [rdx + rdx]
mov rdx, r12
mulx r15, r12, [ rsi + 0x8 ]
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0x98 ], r13
mov r13, rbx
and r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa0 ], r13
mov [ rsp + 0xa8 ], r8
mulx r8, r13, [ rsp - 0x18 ]
mov rdx, r14
mov [ rsp + 0xb0 ], r9
mulx r9, r14, [ rsi + 0x0 ]
shrd rbx, r10, 58
shr r10, 58
add r13, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
mov [ rsp + 0xb8 ], r9
mov [ rsp + 0xc0 ], r14
mulx r14, r9, [ rsi + 0x38 ]
add r9, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x38 ]
add r13, rcx
adcx r8, [ rsp + 0x70 ]
test al, al
adox r13, r12
adox r15, r8
adcx r9, rdi
adcx r14, [ rsp + 0xb0 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, rdi, rax
mov rdx, r11
mulx rax, r11, [ rsi + 0x0 ]
xor r8, r8
adox r13, rdi
adox r12, r15
adcx r13, rbx
adcx r10, r12
mov rbx, r13
shrd rbx, r10, 58
shr r10, 58
mov r15, [ rsp + 0x90 ]
add r15, [ rsp + 0xa8 ]
mov rdi, [ rsp + 0x88 ]
adcx rdi, [ rsp + 0x98 ]
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r14
mulx r14, r8, [ rsp - 0x18 ]
xor rdx, rdx
adox r15, r11
adox rax, rdi
adcx r15, rbx
adcx r10, rax
mov r11, r15
shrd r11, r10, 58
shr r10, 58
mov rdx, r12
mulx rbx, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r12
adox rbx, [ rsp + 0xc8 ]
mov rdi, 0x3ffffffffffffff 
and r13, rdi
mov rdx, rbp
mulx rax, rbp, [ rsi + 0x0 ]
adox r9, rbp
adox rax, rbx
adcx r9, r11
adcx r10, rax
mulx r12, r11, [ rsi + 0x18 ]
mov rbx, r9
shrd rbx, r10, 58
shr r10, 58
mulx rax, rbp, [ rsi + 0x10 ]
imul rdx, [ rsi + 0x40 ], 0x2
and r9, rdi
and r15, rdi
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x20 ], r15
mov r15, r8
adox r15, [ rsp + 0x68 ]
adox r14, [ rsp + 0x60 ]
adcx r15, rbx
adcx r10, r14
mulx rbx, r8, [ rsi + 0x40 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], r9
mulx r9, rdi, rdx
add r8, [ rsp + 0x48 ]
adcx rbx, [ rsp + 0x40 ]
test al, al
adox r8, rbp
adox rax, rbx
adcx rdi, r11
adcx r12, r9
mov rdx, [ rsp - 0x18 ]
mulx rbp, r11, [ rsi + 0x8 ]
test al, al
adox r8, r11
adox rbp, rax
mov r9, r15
shrd r9, r10, 58
shr r10, 58
xor rbx, rbx
adox r8, [ rsp + 0xc0 ]
adox rbp, [ rsp + 0xb8 ]
mulx r11, rax, [ rsi + 0x10 ]
adcx r8, r9
adcx r10, rbp
xor rdx, rdx
adox rdi, rax
adox r11, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, rcx
adcx rdi, rbx
adcx r12, r11
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, r14
mov rdx, r8
shrd rdx, r10, 58
shr r10, 58
xor r14, r14
adox rdi, rcx
adox r9, r12
adcx rdi, rdx
adcx r10, r9
mov rbp, rdi
shrd rbp, r10, 57
shr r10, 57
mov rax, 0x3ffffffffffffff 
and r8, rax
adox rbp, [ rsp + 0x80 ]
adox r10, r14
mov r11, rbp
shrd r11, r10, 58
and rbp, rax
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], rbp
add r11, [ rsp + 0x78 ]
mov r12, r11
shr r12, 58
and r11, rax
mov [ rbx + 0x18 ], r13
add r12, [ rsp + 0xa0 ]
and r15, rax
mov r13, 0x1ffffffffffffff 
and rdi, r13
mov [ rbx + 0x40 ], rdi
mov [ rbx + 0x30 ], r15
mov rcx, [ rsp + 0xd0 ]
mov [ rbx + 0x28 ], rcx
mov [ rbx + 0x8 ], r11
mov [ rbx + 0x10 ], r12
mov [ rbx + 0x38 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 344
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4276
; seed 1456867061767208 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2475036 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=150, initial num_batches=31): 99953 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04038446309467822
; number reverted permutation / tried permutation: 72979 / 89990 =81.097%
; number reverted decision / tried decision: 66145 / 90009 =73.487%
; validated in 1.302s
