SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 456
mov rax, [ rsi + 0x18 ]
lea r10, [rax + rax]
imul rax, [ rsi + 0x28 ], 0x2
mov rdx, [ rsi + 0x30 ]
mulx rcx, r11, rdx
mov rdx, 0x1 
shlx r8, [ rsi + 0x38 ], rdx
mov rdx, r10
mulx r9, r10, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r8
mov rdx, r8
mov [ rsp - 0x48 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov [ rsp - 0x30 ], r10
mov r10, [ rsi + 0x30 ]
mov [ rsp - 0x28 ], rdi
mov rdi, r10
shl rdi, 0x1
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rbp
mulx rbp, r15, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r15
mulx r15, rbp, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], rbp
mulx rbp, r15, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r8
lea r8, [rdx + rdx]
mov rdx, r15
test al, al
adox rdx, r15
mov [ rsp + 0x18 ], r8
mov r8, rbp
adox r8, rbp
xchg rdx, rdi
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], r13
mulx r13, r14, [ rsi + 0x18 ]
xchg rdx, rax
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r14
mov [ rsp + 0x48 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r8
mov r8, r11
adcx r8, rbx
mov [ rsp + 0x58 ], rdi
mov rdi, r9
adcx rdi, rcx
mov [ rsp + 0x60 ], r13
mov r13, r8
add r13, r11
adcx rcx, rdi
add r15, r14
adcx rbp, [ rsp + 0x60 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r15
mulx r15, rbp, rdx
test al, al
adox r8, rbp
mov rdx, r15
adox rdx, rdi
adcx r13, rbx
adcx r9, rcx
mov rbx, 0x1 
shlx rdi, [ rsi + 0x10 ], rbx
mov rcx, r14
test al, al
adox rcx, [ rsp + 0x58 ]
mov rbx, [ rsp + 0x60 ]
adox rbx, [ rsp + 0x50 ]
mov r14, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x78 ], rbx
mov [ rsp + 0x80 ], rcx
mulx rcx, rbx, rdx
mov rdx, rbx
adcx rdx, rbx
mov [ rsp + 0x88 ], rdi
mov rdi, rcx
adcx rdi, rcx
add r13, rbp
adcx r15, r9
add rbx, [ rsp + 0x28 ]
adcx rcx, [ rsp + 0x20 ]
add rdx, [ rsp + 0x28 ]
adcx rdi, [ rsp + 0x20 ]
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], r15
mulx r15, r9, rax
add rbx, r9
mov rdx, r15
adcx rdx, rcx
test al, al
adox rbp, r9
adox r15, rdi
adcx rbp, [ rsp + 0x10 ]
adcx r15, [ rsp - 0x18 ]
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, rdi, rdx
xor rdx, rdx
adox rbx, [ rsp + 0x10 ]
adox rcx, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r12
mulx r12, r13, rdx
adcx rbp, r13
adcx r12, r15
add rbx, rdi
adcx r9, rcx
mov rdx, rax
mulx r15, rax, [ rsi + 0x28 ]
test al, al
adox rax, [ rsp - 0x20 ]
adox r15, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x8 ]
adcx r14, [ rsp - 0x10 ]
mov rdi, rdx
mov rdx, [ rsp + 0x18 ]
mulx r13, rcx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r14
mov r14, rax
mov [ rsp + 0xc0 ], r8
xor r8, r8
adox r14, r9
adox rbx, r15
adcx rbp, rcx
adcx r13, r12
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, rcx, [ rsp + 0x88 ]
test al, al
adox rax, rcx
adox r9, r15
mov rdx, rdi
mulx r15, rdi, [ rsi + 0x8 ]
adcx rax, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov rcx, rdx
mov rdx, [ rsp + 0xa0 ]
mov [ rsp + 0xc8 ], r13
mulx r13, r8, [ rsi + 0x8 ]
mov rdx, rcx
mov [ rsp + 0xd0 ], rbp
mulx rbp, rcx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r13
mov r13, [ rsp + 0x98 ]
add r13, [ rsp - 0x8 ]
mov [ rsp + 0xe0 ], r8
mov r8, [ rsp + 0x90 ]
adcx r8, [ rsp - 0x10 ]
mov [ rsp + 0xe8 ], r8
xor r8, r8
adox r14, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x40 ]
adcx r14, rdi
adcx r15, rbx
mov rdi, rax
shrd rdi, r9, 56
add r13, rcx
mov r9, rbp
adcx r9, [ rsp + 0xe8 ]
mov rbx, rcx
mov [ rsp + 0xf0 ], rdi
xor rdi, rdi
adox rbx, [ rsp + 0xc0 ]
adox rbp, [ rsp + 0xb8 ]
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rcx, rdx
adcx r13, rcx
adcx rdi, r9
add rbx, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r9, rdx
test al, al
adox rbx, r9
adox rcx, rbp
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, r10
adcx r14, rbp
adcx r9, r15
mov rdx, [ rsi + 0x10 ]
mulx rbp, r15, r10
mov rdx, [ rsi + 0x8 ]
lea r10, [rdx + rdx]
test al, al
adox r13, [ rsp + 0x8 ]
adox rdi, [ rsp + 0x0 ]
adcx r13, [ rsp + 0xe0 ]
adcx rdi, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], rbp
mov [ rsp + 0x100 ], r15
mulx r15, rbp, r12
xor rdx, rdx
adox r13, rbp
adox r15, rdi
mov rdi, 0x38 
bzhi rbp, r14, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rbp
mulx rbp, rdi, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], rbp
mulx rbp, r12, r10
shrd r14, r9, 56
xor rdx, rdx
adox r13, [ rsp + 0xf0 ]
adox r15, rdx
mov r9, r14
adcx r9, r13
adc r15, 0x0
mov r10, r9
shrd r10, r15, 56
mov r13, [ rsp + 0x80 ]
test al, al
adox r13, [ rsp + 0x38 ]
mov r15, [ rsp + 0x78 ]
adox r15, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], r10
mov [ rsp + 0x120 ], rdi
mulx rdi, r10, r11
adcx r14, rbx
adc rcx, 0x0
mov rdx, [ rsp + 0x70 ]
add rdx, [ rsp + 0x38 ]
mov rbx, [ rsp + 0x68 ]
adcx rbx, [ rsp + 0x30 ]
mov [ rsp + 0x128 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], rbp
mulx rbp, r10, r8
mov rdx, r14
shrd rdx, rcx, 56
add r13, [ rsp + 0x100 ]
adcx r15, [ rsp + 0xf8 ]
test al, al
adox r13, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
adcx rdi, [ rsp + 0x100 ]
adcx rbx, [ rsp + 0xf8 ]
xor r8, r8
adox rdi, r12
adox rbx, [ rsp + 0x138 ]
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, r11
adcx rdi, r12
adc rbx, 0x0
mov rdx, 0x38 
bzhi r11, rdi, rdx
adox r13, [ rsp + 0x120 ]
adox r15, [ rsp + 0x110 ]
test al, al
adox r13, [ rsp + 0x130 ]
adox r15, [ rsp + 0x128 ]
adcx r13, [ rsp + 0x118 ]
adc r15, 0x0
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x140 ], r11
mulx r11, r12, [ rsi + 0x0 ]
mov rdx, rcx
add rdx, [ rsp + 0xd0 ]
adcx r8, [ rsp + 0xc8 ]
test al, al
adox rdx, r10
adox rbp, r8
mov r10, 0x38 
bzhi rcx, r13, r10
shrd r13, r15, 56
shrd rdi, rbx, 56
bzhi rbx, rax, r10
mov rax, r12
adox rax, [ rsp + 0xb0 ]
adox r11, [ rsp + 0xa8 ]
add rax, rdi
adc r11, 0x0
mov r15, rax
shrd r15, r11, 56
lea r15, [ r15 + rbx ]
xor r12, r12
adox rdx, r13
adox rbp, r12
bzhi r8, r15, r10
mov r13, rdx
shrd r13, rbp, 56
add r13, [ rsp + 0x108 ]
mov rdi, r13
shr rdi, 56
bzhi rbx, r9, r10
bzhi r9, r13, r10
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x38 ], r9
bzhi rbp, r14, r10
lea rbx, [ rbx + rdi ]
lea rbp, [ rbp + rdi ]
bzhi r14, rbp, r10
mov [ r11 + 0x0 ], r14
shr rbp, 56
shr r15, 56
add rbp, [ rsp + 0x140 ]
lea r15, [ r15 + rbx ]
mov r13, r15
shr r13, 56
lea r13, [ r13 + rcx ]
bzhi rcx, r15, r10
bzhi rdi, rdx, r10
mov [ r11 + 0x20 ], rcx
mov [ r11 + 0x18 ], r8
mov [ r11 + 0x28 ], r13
bzhi rdx, rax, r10
mov [ r11 + 0x8 ], rbp
mov [ r11 + 0x10 ], rdx
mov [ r11 + 0x30 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 456
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.0506
; seed 4497829927516477 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2375104 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=229, initial num_batches=31): 104326 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0439248133976449
; number reverted permutation / tried permutation: 67950 / 90015 =75.487%
; number reverted decision / tried decision: 62042 / 89984 =68.948%
; validated in 1.015s
