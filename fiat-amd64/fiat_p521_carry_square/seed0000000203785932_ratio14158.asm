SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 368
mov rax, [ rsi + 0x28 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x28 ]
lea r11, [ 4 * rax]
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, rdx
imul rdx, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov rdx, 0x1 
mov [ rsp - 0x58 ], r15
shlx r15, [ rsi + 0x38 ], rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r10
imul rdx, [ rsi + 0x20 ], 0x2
mov [ rsp - 0x40 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], rdi
mulx rdi, r14, r10
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x28 ], r13
mov r13, rdx
shl r13, 0x2
mov rdx, r13
mov [ rsp - 0x20 ], r15
mulx r15, r13, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], rax
mulx rax, rcx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], rax
mov [ rsp + 0x10 ], rcx
mulx rcx, rax, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], rcx
mov rcx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rax
mov rax, rcx
shl rax, 0x1
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], r12
mulx r12, rbp, rax
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], r12
mulx r12, rax, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x40 ], rbp
mov rbp, rdx
shl rbp, 0x2
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], rbx
mulx rbx, r11, rbp
imul rdx, [ rsi + 0x18 ], 0x2
mov [ rsp + 0x58 ], r15
xor r15, r15
adox rax, r11
adox rbx, r12
imul r12, [ rsi + 0x38 ], 0x4
mulx r15, r11, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r15
mov [ rsp + 0x68 ], r11
mulx r11, r15, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r11
mov [ rsp + 0x78 ], r15
mulx r15, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r15
mov [ rsp + 0x88 ], r11
mulx r11, r15, r12
xor rdx, rdx
adox rax, r15
adox r11, rbx
adcx r8, r14
adcx rdi, r9
test al, al
adox rax, r13
adox r11, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, rbp
adcx r8, r9
adcx r14, rdi
mov rdx, [ rsp + 0x48 ]
mulx rdi, r15, [ rsi + 0x20 ]
add r15, r13
adcx rbx, rdi
test al, al
adox rax, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x28 ]
mulx r13, r9, rbp
mov rdx, r12
mulx rbp, r12, [ rsi + 0x10 ]
mov [ rsp + 0x90 ], r14
mulx r14, rdi, [ rsi + 0x20 ]
adcx r15, r12
adcx rbp, rbx
xor rbx, rbx
adox r9, rdi
adox r14, r13
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mulx rdi, r12, [ rsp + 0x50 ]
adcx r9, [ rsp + 0x30 ]
adcx r14, [ rsp + 0x28 ]
test al, al
adox r15, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x8 ]
adcx r15, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
mov rdx, r13
mulx rbx, r13, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], r14
mulx r14, r8, [ rsi + 0x28 ]
xor rdx, rdx
adox r13, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x18 ]
adcx r12, r8
adcx r14, rdi
mov rdx, [ rsi + 0x20 ]
mulx r8, rdi, rcx
add r13, [ rsp - 0x10 ]
adcx rbx, [ rsp - 0x18 ]
xor rdx, rdx
adox r12, rdi
adox r8, r14
mov r14, [ rsi + 0x10 ]
mov rdi, r14
shl rdi, 0x1
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rbx
mulx rbx, r14, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], r9
mulx r9, r13, rdi
mov rdx, 0x3a 
bzhi rdi, r15, rdx
shrd r15, rbp, 58
shr rbp, 58
test al, al
adox rax, r15
adox rbp, r11
adcx r12, r14
adcx rbx, r8
mov rdx, rcx
mulx r11, rcx, [ rsi + 0x38 ]
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, rdx
mov rdx, 0x3ffffffffffffff 
mov [ rsp + 0xc0 ], rdi
mov rdi, rax
and rdi, rdx
mov rdx, r14
adox rdx, [ rsp + 0xb8 ]
adox r15, [ rsp + 0xa0 ]
mov r14, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], rbx
mulx rbx, rdi, [ rsp - 0x20 ]
mov rdx, r8
mov [ rsp + 0xd8 ], r12
mulx r12, r8, [ rsi + 0x30 ]
adcx rdi, r8
adcx r12, rbx
mov rdx, [ rsi + 0x18 ]
mulx r8, rbx, rdx
add rcx, rbx
adcx r8, r11
xor rdx, rdx
adox rdi, [ rsp + 0x68 ]
adox r12, [ rsp + 0x60 ]
adcx r14, r13
adcx r9, r15
shrd rax, rbp, 58
shr rbp, 58
mov rdx, [ rsi + 0x8 ]
mulx r11, r13, [ rsp - 0x28 ]
add r14, rax
adcx rbp, r9
mov rdx, r14
shrd rdx, rbp, 58
shr rbp, 58
xor r15, r15
adox rdi, r13
adox r11, r12
mov rbx, [ rsp + 0x88 ]
mov r12, rbx
adcx r12, [ rsp + 0xd8 ]
mov r9, [ rsp + 0x80 ]
adcx r9, [ rsp + 0xd0 ]
mov rbx, [ rsp + 0x78 ]
mov rax, rbx
test al, al
adox rax, [ rsp + 0xb0 ]
mov r13, [ rsp + 0x70 ]
adox r13, [ rsp + 0xa8 ]
adcx r12, rdx
adcx rbp, r9
mov rbx, r12
shrd rbx, rbp, 58
shr rbp, 58
mov rdx, [ rsi + 0x0 ]
mulx r15, r9, [ rsp - 0x28 ]
xor rdx, rdx
adox rax, r9
adox r15, r13
mov rdx, [ rsp - 0x28 ]
mulx r9, r13, [ rsi + 0x18 ]
adcx rax, rbx
adcx rbp, r15
mov rbx, 0x3ffffffffffffff 
and r12, rbx
mov r15, rax
shrd r15, rbp, 58
shr rbp, 58
mov [ rsp + 0xe0 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
add rcx, rbx
adcx r9, r8
xor rdx, rdx
adox rcx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
mov rdx, r10
mulx r8, r10, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r12
adcx rdi, r10
adcx r8, r11
test al, al
adox rdi, r15
adox rbp, r8
imul r11, [ rsi + 0x40 ], 0x2
mov r12, 0x3a 
bzhi r15, rdi, r12
mov rbx, rdx
mov rdx, [ rsp + 0x50 ]
mulx r8, r10, [ rsi + 0x0 ]
xchg rdx, r11
mulx rbx, r12, [ rsi + 0x40 ]
mov [ rsp + 0xe8 ], r9
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x28 ], r15
adox r12, r13
adox rbx, [ rsp + 0xe0 ]
xor r13, r13
adox rcx, r10
adox r8, [ rsp + 0xe8 ]
shrd rdi, rbp, 58
shr rbp, 58
xchg rdx, r11
mulx r10, r15, [ rsi + 0x8 ]
test al, al
adox rcx, rdi
adox rbp, r8
adcx r12, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
mov rdx, rcx
shrd rdx, rbp, 58
shr rbp, 58
mov r8, rdx
mov rdx, [ rsp - 0x20 ]
mulx r13, rdi, [ rsi + 0x8 ]
xor r9, r9
adox r12, r15
adox r10, rbx
mulx rbx, r15, [ rsi + 0x0 ]
adcx r12, r15
adcx rbx, r10
test al, al
adox r12, r8
adox rbp, rbx
mov rdx, r12
shrd rdx, rbp, 58
shr rbp, 58
mov r8, 0x3a 
bzhi r10, rcx, r8
mov rcx, rdi
adox rcx, [ rsp + 0x98 ]
adox r13, [ rsp + 0x90 ]
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, r11
xor rdx, rdx
adox rcx, r15
adox rbx, r13
adcx rcx, rdi
adcx rbp, rbx
mov r9, 0x39 
bzhi r11, rcx, r9
shrd rcx, rbp, 57
shr rbp, 57
bzhi rdi, r14, r8
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x40 ], r11
adox rcx, [ rsp + 0xc0 ]
adox rbp, rdx
bzhi r13, rcx, r8
shrd rcx, rbp, 58
mov [ r14 + 0x0 ], r13
add rcx, [ rsp + 0xc8 ]
bzhi r15, rcx, r8
shr rcx, 58
lea rcx, [ rcx + rdi ]
mov [ r14 + 0x10 ], rcx
mov [ r14 + 0x8 ], r15
bzhi rbx, r12, r8
mov [ r14 + 0x38 ], rbx
bzhi r12, rax, r8
mov [ r14 + 0x30 ], r10
mov [ r14 + 0x20 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 368
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4158
; seed 3378697943203287 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4513209 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=145, initial num_batches=31): 177097 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.039239707268154435
; number reverted permutation / tried permutation: 66447 / 90075 =73.769%
; number reverted decision / tried decision: 60731 / 89924 =67.536%
; validated in 2.857s
