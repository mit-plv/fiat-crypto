SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 272
mov rax, [ rsi + 0x10 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x40 ]
lea r11, [ 4 * rax]
mov rax, [ rsi + 0x28 ]
lea rdx, [rax + rax]
mulx rcx, rax, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov rbx, [ rsi + 0x30 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [rbx + rbx]
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rdi
mulx rdi, rcx, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], rax
lea rax, [ 4 * rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r8
mulx r8, r9, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r15
mulx r15, r10, rax
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], r14
mov r14, rdx
shl r14, 0x2
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r9
mulx r9, r8, rbx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], rcx
mulx rcx, rdi, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], rdi
mulx rdi, rcx, rax
add r8, rcx
adcx rdi, r9
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, r14
add r8, r9
adcx rcx, rdi
mov rdx, [ rsi + 0x28 ]
mov rdi, rdx
shl rdi, 0x2
mov rdx, rdi
mulx r9, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r12
mulx r12, r13, rbx
mov rdx, rbx
mov [ rsp + 0x38 ], r12
mulx r12, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], rcx
mulx rcx, r13, rdx
test al, al
adox r13, rbx
adox r12, rcx
adcx rdi, r10
adcx r15, r9
mov rdx, [ rsi + 0x30 ]
mulx r9, r10, rbp
mov rdx, [ rsi + 0x28 ]
mulx rcx, rbx, r14
add r10, rbx
adcx rcx, r9
mov rdx, [ rsi + 0x10 ]
mulx rbx, r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r12
mov r12, rdx
shl r12, 0x1
xor rdx, rdx
adox r8, r9
adox rbx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], r13
mulx r13, r9, r14
adcx rdi, r9
adcx r13, r15
mov rdx, [ rsi + 0x20 ]
mulx r9, r15, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], rcx
mulx rcx, r14, r12
test al, al
adox r8, r14
adox rcx, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r12, r11
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], rcx
mulx rcx, r14, rax
adcx r14, r15
adcx r9, rcx
mov rdx, [ rsi + 0x0 ]
mulx r15, rax, rdx
add rdi, r12
adcx rbx, r13
add rdi, rax
adcx r15, rbx
mov rdx, rdi
shrd rdx, r15, 58
shr r15, 58
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r12, rdx
mov rdx, 0x3ffffffffffffff 
and rdi, rdx
mov rdx, r11
mulx rax, r11, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
adox r14, rbx
adox rdi, r9
adcx r10, r11
adcx rax, [ rsp + 0x60 ]
add r14, r12
adcx rcx, rdi
mov r9, [ rsp + 0x20 ]
xor r12, r12
adox r9, [ rsp + 0x30 ]
mov r11, [ rsp + 0x18 ]
adox r11, [ rsp + 0x28 ]
adcx r8, r13
adcx r15, [ rsp + 0x68 ]
xor r13, r13
adox r10, [ rsp + 0x10 ]
adox rax, [ rsp + 0x8 ]
adcx r14, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x8 ]
mov r12, 0x3a 
bzhi rbx, r8, r12
imul rdi, [ rsi + 0x18 ], 0x2
shrd r8, r15, 58
shr r15, 58
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], rbx
mulx rbx, r12, rdi
add r14, r8
adcx r15, rcx
mov rdx, r14
shrd rdx, r15, 58
shr r15, 58
xor rcx, rcx
adox r10, r12
adox rbx, rax
adcx r10, rdx
adcx r15, rbx
mov rax, 0x3a 
bzhi r8, r10, rax
imul r12, [ rsi + 0x20 ], 0x2
imul rdx, [ rsi + 0x38 ], 0x2
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], r12
mulx r12, rbx, rdi
add r9, rcx
adcx rax, r11
add r9, rbx
adcx r12, rax
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r8
mov r11, rdx
mov rdx, [ rsp + 0x88 ]
mulx rcx, r8, [ rsi + 0x0 ]
shrd r10, r15, 58
shr r15, 58
test al, al
adox r9, r8
adox rcx, r12
adcx r9, r10
adcx r15, rcx
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mulx r12, rax, [ rsp + 0x80 ]
mov rdx, 0x3a 
bzhi r8, r9, rdx
shrd r9, r15, 58
shr r15, 58
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, rdi
xor rdx, rdx
adox rax, [ rsp - 0x10 ]
adox r12, [ rsp - 0x18 ]
mov rdx, rbx
mulx rdi, rbx, [ rsi + 0x8 ]
adcx rax, r10
adcx rcx, r12
xor r10, r10
adox rax, rbx
adox rdi, rcx
mov [ r11 + 0x20 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r12, rbp
adcx rax, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
add rax, r9
adcx r15, rdi
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, rdx
mov rdx, [ rsi + 0x38 ]
mulx r10, rdi, r13
mov rdx, rax
shrd rdx, r15, 58
shr r15, 58
xor r13, r13
adox rdi, r9
adox rcx, r10
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r10, r8
adcx rdi, r10
adcx r13, rcx
test al, al
adox rdi, [ rsp - 0x30 ]
adox r13, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, r8
mov rdx, 0x1 
shlx r8, [ rsi + 0x40 ], rdx
adcx rdi, r12
adcx rbx, r13
mov rdx, [ rsi + 0x40 ]
mulx r13, r12, r8
xor rdx, rdx
adox rdi, r9
adox r15, rbx
mov rdx, rbp
mulx r9, rbp, [ rsi + 0x8 ]
adcx r12, rcx
adcx r10, r13
mov rdx, [ rsi + 0x0 ]
mulx rbx, rcx, [ rsp + 0x80 ]
xor rdx, rdx
adox r12, [ rsp + 0x40 ]
adox r10, [ rsp + 0x38 ]
adcx r12, rbp
adcx r9, r10
mov r13, 0x3a 
bzhi rbp, rdi, r13
adox r12, rcx
adox rbx, r9
mov rdx, [ rsi + 0x8 ]
mulx r10, rcx, [ rsp + 0x80 ]
mov rdx, [ rsp - 0x38 ]
mov r9, rdx
add r9, [ rsp + 0x58 ]
mov r13, [ rsp - 0x40 ]
adcx r13, [ rsp + 0x50 ]
mov [ r11 + 0x30 ], rbp
shrd rdi, r15, 58
shr r15, 58
add r12, rdi
adcx r15, rbx
mov rdx, r8
mulx rbp, r8, [ rsi + 0x0 ]
mov rdx, r12
shrd rdx, r15, 58
shr r15, 58
test al, al
adox r9, rcx
adox r10, r13
adcx r9, r8
adcx rbp, r10
xor rbx, rbx
adox r9, rdx
adox r15, rbp
mov rcx, r9
shrd rcx, r15, 57
shr r15, 57
add rcx, [ rsp + 0x70 ]
adc r15, 0x0
mov r13, 0x3a 
bzhi rdi, rcx, r13
shrd rcx, r15, 58
add rcx, [ rsp + 0x78 ]
bzhi r8, rcx, r13
shr rcx, 58
bzhi rdx, r14, r13
mov [ r11 + 0x8 ], r8
lea rcx, [ rcx + rdx ]
bzhi r14, rax, r13
bzhi rax, r12, r13
mov [ r11 + 0x28 ], r14
mov r12, 0x39 
bzhi r10, r9, r12
mov [ r11 + 0x40 ], r10
mov [ r11 + 0x10 ], rcx
mov [ r11 + 0x0 ], rdi
mov [ r11 + 0x38 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 272
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5196
; seed 3127531783157201 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4338926 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=148, initial num_batches=31): 178598 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.041161799025841876
; number reverted permutation / tried permutation: 65111 / 89728 =72.565%
; number reverted decision / tried decision: 60164 / 90271 =66.648%
; validated in 2.841s
