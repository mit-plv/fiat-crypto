SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 432
mov rax, [ rsi + 0x28 ]
mov r10, rax
shl r10, 0x1
mov rax, [ rsi + 0x38 ]
lea r11, [rax + rax]
mov rdx, [ rsi + 0x28 ]
mulx rcx, rax, rdx
mov rdx, [ rsi + 0x30 ]
lea r8, [rdx + rdx]
mov rdx, r11
mulx r9, r11, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
shl r13, 0x1
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbp
lea rbp, [rdx + rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r11
mulx r11, r9, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r14
mulx r14, r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r12
mulx r12, rbp, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rbp
mulx rbp, r12, r10
mov rdx, rbx
mov [ rsp + 0x10 ], rbp
mulx rbp, rbx, [ rsi + 0x30 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], r12
mov [ rsp + 0x38 ], r13
mulx r13, r12, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r11
mov [ rsp + 0x48 ], r9
mulx r9, r11, r8
mov rdx, r8
mov [ rsp + 0x50 ], r9
mulx r9, r8, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r11
mov r11, rbx
mov [ rsp + 0x60 ], r9
xor r9, r9
adox r11, r12
mov [ rsp + 0x68 ], r8
mov r8, r13
adox r8, rbp
mov [ rsp + 0x70 ], r8
mov r8, rbx
adcx r8, rbx
adcx rbp, rbp
mov rbx, r15
add rbx, r15
mov [ rsp + 0x78 ], r11
mov r11, r14
adcx r11, r14
add rbx, rax
mov [ rsp + 0x80 ], rbp
mov rbp, rcx
adcx rbp, r11
test al, al
adox r15, rax
adox rcx, r14
mov rax, 0x1 
shlx r14, [ rsi + 0x18 ], rax
adcx rbx, [ rsp + 0x68 ]
adcx rbp, [ rsp + 0x60 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r9, r14
xor rdx, rdx
adox r8, r12
adox r13, [ rsp + 0x80 ]
mov rdx, rdi
mulx r12, rdi, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], rax
mov rax, rdi
adcx rax, [ rsp + 0x48 ]
mov [ rsp + 0x90 ], r9
mov r9, r12
adcx r9, [ rsp + 0x40 ]
test al, al
adox r8, [ rsp + 0x58 ]
adox r13, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x68 ]
adcx rcx, [ rsp + 0x60 ]
mov [ rsp + 0x98 ], r13
mov r13, rax
mov [ rsp + 0xa0 ], r8
xor r8, r8
adox r13, [ rsp + 0x48 ]
mov [ rsp + 0xa8 ], rcx
mov rcx, r9
adox rcx, [ rsp + 0x40 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], r15
mov [ rsp + 0xb8 ], rbp
mulx rbp, r15, rdx
adcx r13, rdi
adcx r12, rcx
add r13, r15
mov rdx, rbp
adcx rdx, r12
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, r10
xor rdx, rdx
adox r13, rcx
mov r10, r12
adox r10, rdi
adcx rax, r15
adcx rbp, r9
mov rdx, r11
mulx r9, r11, [ rsi + 0x10 ]
test al, al
adox rax, rcx
adox r12, rbp
adcx rax, r11
mov r15, r9
adcx r15, r12
xor rdi, rdi
adox r13, r11
adox r9, r10
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, [ rsp + 0x38 ]
mov rdx, rcx
mulx r11, rcx, [ rsi + 0x28 ]
adcx rcx, [ rsp + 0x20 ]
adcx r11, [ rsp - 0x10 ]
add rax, [ rsp + 0x30 ]
adcx r15, [ rsp + 0x28 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r15
mulx r15, rdi, r8
xor rdx, rdx
adox rbx, rdi
mov [ rsp + 0xc8 ], rax
mov rax, r15
adox rax, [ rsp + 0xb8 ]
mov [ rsp + 0xd0 ], rax
mov rax, rdi
adcx rax, [ rsp + 0xb0 ]
adcx r15, [ rsp + 0xa8 ]
mov rdi, rcx
add rdi, r10
adcx rbp, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], rbx
mulx rbx, r10, [ rsp - 0x18 ]
test al, al
adox rcx, r10
adox rbx, r11
mov rdx, r14
mulx r11, r14, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], r15
mulx r15, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe8 ], rax
mov [ rsp + 0xf0 ], r11
mulx r11, rax, rdx
adcx r13, rax
adcx r11, r9
test al, al
adox rcx, r10
adox r15, rbx
mov rdx, [ rsp + 0x78 ]
adcx rdx, [ rsp + 0x58 ]
mov r9, [ rsp + 0x70 ]
adcx r9, [ rsp + 0x50 ]
test al, al
adox rdi, [ rsp + 0x8 ]
adox rbp, [ rsp - 0x8 ]
adcx rdi, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
xor rbx, rbx
adox r13, [ rsp + 0x30 ]
adox r11, [ rsp + 0x28 ]
mov r10, rcx
shrd r10, r15, 56
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, rdx
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0xf8 ], r10
mov [ rsp + 0x100 ], r11
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r11
mov [ rsp + 0x110 ], r10
mulx r10, r11, [ rsp + 0x38 ]
mov rdx, 0xffffffffffffff 
and rcx, rdx
mov rdx, r8
mov [ rsp + 0x118 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
adox rax, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx rdi, r8
adcx rcx, rbp
mov rdx, rdi
shrd rdx, rcx, 56
mov rbp, r15
xor r8, r8
adox rbp, [ rsp + 0xc8 ]
adox rbx, [ rsp + 0xc0 ]
mov r15, rdx
adcx r15, rbp
adc rbx, 0x0
mov rcx, r15
shrd rcx, rbx, 56
xor rbp, rbp
adox r13, r14
mov r8, [ rsp + 0x100 ]
adox r8, [ rsp + 0xf0 ]
adcx r13, r11
adcx r10, r8
add r13, [ rsp + 0xf8 ]
adc r10, 0x0
test al, al
adox rdx, r13
adox r10, rbp
mov r14, rdx
shrd r14, r10, 56
mov r11, 0xffffffffffffff 
and r15, r11
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r8, [ rsp + 0x38 ]
mov rdx, [ rsp + 0xa0 ]
adox rdx, [ rsp - 0x30 ]
mov r10, [ rsp + 0x98 ]
adox r10, [ rsp - 0x38 ]
adcx rdx, [ rsp + 0x90 ]
adcx r10, [ rsp + 0x88 ]
xor r11, r11
adox rax, [ rsp + 0x110 ]
adox r9, [ rsp + 0x108 ]
mov rbp, rdx
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0x120 ], r15
mulx r15, r11, [ rsi + 0x0 ]
adcx rax, rcx
adc r9, 0x0
mov rdx, rax
shrd rdx, r9, 56
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], r14
mulx r14, r9, rdx
mov rdx, r9
add rdx, [ rsp + 0xe8 ]
adcx r14, [ rsp + 0xe0 ]
add rdx, r11
adcx r15, r14
test al, al
adox rdx, rcx
mov r11, 0x0 
adox r15, r11
mov rcx, rdx
shrd rcx, r15, 56
test al, al
adox rbp, r8
adox r13, r10
mov r8, 0xffffffffffffff 
and rdx, r8
and rdi, r8
adox rbp, [ rsp + 0x18 ]
adox r13, [ rsp + 0x10 ]
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, rdx
adcx rbp, [ rsp + 0x128 ]
adc r13, 0x0
mov rdx, [ rsp + 0x38 ]
mulx r11, r15, [ rsi + 0x10 ]
add rcx, [ rsp + 0x118 ]
mov rdx, rcx
and rdx, r8
shr rcx, 56
mov r8, r9
test al, al
adox r8, [ rsp + 0xd8 ]
adox r14, [ rsp + 0xd0 ]
adcx r8, r15
adcx r11, r14
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x18 ], rdx
mov rdx, r12
mulx r15, r12, [ rsi + 0x0 ]
test al, al
adox r8, [ rsp - 0x40 ]
adox r11, [ rsp - 0x48 ]
mov rdx, rbp
shrd rdx, r13, 56
xor r13, r13
adox r8, r12
adox r15, r11
adcx r8, rdx
adc r15, 0x0
mov r14, r8
shrd r14, r15, 56
mov r12, 0x38 
bzhi r11, r8, r12
lea r14, [ r14 + rdi ]
mov rdi, r14
shr rdi, 56
mov rdx, rdi
add rdx, [ rsp + 0x120 ]
bzhi r8, rdx, r12
bzhi r15, rbx, r12
bzhi rbx, rax, r12
lea r15, [ r15 + rdi ]
shr rdx, 56
lea rcx, [ rcx + r15 ]
lea rdx, [ rdx + rbx ]
bzhi rax, rcx, r12
mov [ r9 + 0x8 ], rdx
mov [ r9 + 0x0 ], r8
bzhi rdi, rbp, r12
shr rcx, 56
lea rcx, [ rcx + rdi ]
mov [ r9 + 0x28 ], rcx
mov [ r9 + 0x10 ], r10
mov [ r9 + 0x30 ], r11
bzhi r10, r14, r12
mov [ r9 + 0x20 ], rax
mov [ r9 + 0x38 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 432
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.0699
; seed 3667742126253595 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2345466 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=229, initial num_batches=31): 103200 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.043999785117328494
; number reverted permutation / tried permutation: 68423 / 90045 =75.988%
; number reverted decision / tried decision: 62304 / 89954 =69.262%
; validated in 1.128s
