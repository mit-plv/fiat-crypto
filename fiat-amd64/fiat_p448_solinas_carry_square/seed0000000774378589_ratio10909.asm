SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 432
mov rax, [ rsi + 0x20 ]
mov r10, rax
shl r10, 0x1
mov rax, 0x1 
shlx r11, [ rsi + 0x28 ], rax
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, r10
shlx rdx, [ rsi + 0x30 ], rax
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, r9
mov [ rsp - 0x58 ], r15
mulx r15, r9, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov rdi, 0x1 
mov [ rsp - 0x48 ], r12
shlx r12, [ rsi + 0x38 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r15
mulx r15, rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r14
mulx r14, r9, r12
mov rdx, r11
mov [ rsp - 0x20 ], r13
mulx r13, r11, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r13
mov r13, 0x1 
mov [ rsp - 0x10 ], r11
shlx r11, [ rsi + 0x8 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r14
mulx r14, r11, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], r9
mulx r9, r10, r12
mov rdx, r12
mov [ rsp + 0x18 ], r14
mulx r14, r12, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], rax
mulx rax, rbx, rdx
mov rdx, rdi
mov [ rsp + 0x38 ], rax
mulx rax, rdi, [ rsi + 0x10 ]
xchg rdx, r11
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rax
mulx rax, rbx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], rdi
mulx rdi, rbx, rdx
mov rdx, r13
mov [ rsp + 0x68 ], rdi
mulx rdi, r13, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], rbx
mov [ rsp + 0x78 ], r9
mulx r9, rbx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r9
mov [ rsp + 0x88 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r9
mov [ rsp + 0xa8 ], rbx
mulx rbx, r9, r11
test al, al
adox r9, r12
adox r14, rbx
mov rdx, r9
adcx rdx, rcx
adcx r8, r14
mov rcx, [ rsi + 0x10 ]
lea r12, [rcx + rcx]
test al, al
adox rdx, r13
adox rdi, r8
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, r12
adcx r9, r13
adcx rbx, r14
mov rdx, [ rsi + 0x30 ]
mulx r8, r14, rdx
mov rdx, rbp
add rdx, rbp
mov r13, r15
adcx r13, r15
mov [ rsp + 0xb0 ], rdi
mov rdi, r14
add rdi, r10
mov [ rsp + 0xb8 ], rcx
mov rcx, r8
adcx rcx, [ rsp + 0x78 ]
add rdx, [ rsp + 0x70 ]
adcx r13, [ rsp + 0x68 ]
mov [ rsp + 0xc0 ], r13
mov r13, rdi
mov [ rsp + 0xc8 ], rdx
xor rdx, rdx
adox r13, r14
adox r8, rcx
mov r14, 0x1 
shlx rdx, [ rsi + 0x18 ], r14
adcx rdi, [ rsp + 0x30 ]
adcx rcx, [ rsp + 0x28 ]
xor r14, r14
adox rdi, [ rsp + 0x88 ]
adox rcx, [ rsp + 0x80 ]
mov [ rsp + 0xd0 ], r8
mulx r8, r14, [ rsi + 0x0 ]
adcx rdi, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x48 ]
mov [ rsp + 0xd8 ], rcx
xor rcx, rcx
adox r9, r14
adox r8, rbx
mov rbx, r9
shrd rbx, r8, 56
mulx r8, r14, [ rsi + 0x10 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r8
mov [ rsp + 0xe8 ], r14
mulx r14, r8, rax
mov rdx, 0xffffffffffffff 
and r9, rdx
mov rdx, r11
mov [ rsp + 0xf0 ], r9
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, r11
adox rdx, [ rsp + 0xb8 ]
adox r9, [ rsp + 0xb0 ]
adcx rbp, [ rsp + 0x70 ]
adcx r15, [ rsp + 0x68 ]
test al, al
adox rdx, r8
adox r14, r9
adcx rbp, [ rsp + 0x20 ]
adcx r15, [ rsp + 0x18 ]
test al, al
adox r13, r10
mov r8, [ rsp + 0xd0 ]
adox r8, [ rsp + 0x78 ]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], r14
mulx r14, rbx, rax
adcx rdi, rbx
mov rdx, r14
adcx rdx, [ rsp + 0xd8 ]
add r13, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
add rdi, [ rsp + 0x40 ]
adcx rdx, [ rsp + 0x38 ]
mov [ rsp + 0x108 ], rdx
xor rdx, rdx
adox r13, [ rsp + 0x88 ]
adox r8, [ rsp + 0x80 ]
adcx rbp, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x0 ]
mov rdx, rcx
mov [ rsp + 0x110 ], r15
mulx r15, rcx, [ rsi + 0x8 ]
add r13, [ rsp + 0x60 ]
adcx r8, [ rsp + 0x48 ]
xor rdx, rdx
adox r13, r11
adox r9, r8
adcx r13, rbx
adcx r14, r9
xor r11, r11
adox r13, rcx
adox r15, r14
mov rdx, [ rsp + 0x20 ]
mov rbx, rdx
adcx rbx, [ rsp + 0xc8 ]
mov rcx, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0xc0 ]
test al, al
adox rbx, [ rsp + 0x10 ]
adox rcx, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r14, [ rsp + 0x8 ]
adcx r13, r14
adcx r11, r15
add rbx, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x28 ]
mov rdx, [ rsp + 0x100 ]
mov r15, r10
shrd r15, rdx, 56
test al, al
adox r13, [ rsp + 0xf8 ]
mov rdx, 0x0 
adox r11, rdx
mov r14, r15
adcx r14, rdi
mov [ rsp + 0x118 ], rcx
mov rcx, [ rsp + 0x108 ]
adc rcx, 0x0
xor rdi, rdi
adox r15, r13
adox r11, rdi
mov rdx, r15
shrd rdx, r11, 56
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mulx rdi, r11, rax
add rbp, r8
adcx r9, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rax, r12
mov rdx, r11
add rdx, [ rsp + 0x98 ]
mov r12, rdi
adcx r12, [ rsp + 0x90 ]
mov [ rsp + 0x120 ], rbx
mov rbx, 0x38 
mov [ rsp + 0x128 ], r13
bzhi r13, r15, rbx
adox rdx, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
xor r15, r15
adox rdx, [ rsp + 0x58 ]
adox r12, [ rsp + 0x50 ]
adcx rbp, rax
adcx r8, r9
mov r9, rdx
mov rdx, [ rsp - 0x8 ]
mulx r15, rax, [ rsi + 0x0 ]
add r9, rax
adcx r15, r12
mov rdx, r14
shrd rdx, rcx, 56
test al, al
adox r9, rdx
mov rcx, 0x0 
adox r15, rcx
mov r12, r9
shrd r12, r15, 56
mov rax, r11
xor rdx, rdx
adox rax, r11
adox rdi, rdi
adcx rax, [ rsp + 0x98 ]
adcx rdi, [ rsp + 0x90 ]
xor rcx, rcx
adox rax, [ rsp - 0x30 ]
adox rdi, [ rsp - 0x38 ]
adcx rax, [ rsp + 0x58 ]
adcx rdi, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r11, [ rsp + 0x8 ]
xor rdx, rdx
adox rbp, r12
adox r8, rdx
adcx rax, [ rsp + 0xe8 ]
adcx rdi, [ rsp + 0xe0 ]
mov rcx, rbp
shrd rcx, r8, 56
test al, al
adox rax, r11
adox r15, rdi
add rcx, [ rsp + 0xf0 ]
xor r12, r12
adox rax, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
bzhi rdx, rbp, rbx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x10 ], rdx
adox rax, [ rsp + 0x128 ]
adox r15, r12
bzhi rbp, rcx, rbx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r8, [ rsp + 0x8 ]
mov rdx, rax
shrd rdx, r15, 56
mov r15, r8
xor rbx, rbx
adox r15, [ rsp + 0x120 ]
adox rdi, [ rsp + 0x118 ]
adcx r15, [ rsp + 0xa8 ]
adcx rdi, [ rsp + 0xa0 ]
xor r12, r12
adox r15, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
adcx r15, rdx
adc rdi, 0x0
mov rbx, r15
shrd rbx, rdi, 56
mov r8, 0xffffffffffffff 
and r15, r8
mov [ r11 + 0x30 ], r15
and r10, r8
lea rbx, [ rbx + r10 ]
mov rdx, rbx
and rdx, r8
shr rbx, 56
and r14, r8
lea r14, [ r14 + rbx ]
mov rdi, r14
and rdi, r8
shr r14, 56
and r9, r8
mov [ r11 + 0x0 ], rdi
lea r14, [ r14 + r9 ]
mov [ r11 + 0x8 ], r14
shr rcx, 56
mov [ r11 + 0x18 ], rbp
lea r13, [ r13 + rbx ]
lea rcx, [ rcx + r13 ]
mov rbp, rcx
and rbp, r8
and rax, r8
shr rcx, 56
lea rcx, [ rcx + rax ]
mov [ r11 + 0x38 ], rdx
mov [ r11 + 0x20 ], rbp
mov [ r11 + 0x28 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 432
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.0909
; seed 2119711715114360 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3147650 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=141, initial num_batches=31): 107282 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03408320493066256
; number reverted permutation / tried permutation: 64309 / 90535 =71.032%
; number reverted decision / tried decision: 57896 / 89464 =64.714%
; validated in 2.042s
