SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 480
mov rdx, [ rsi + 0x28 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx rcx, r11, rdx
mov rdx, 0x1 
shlx r8, [ rsi + 0x28 ], rdx
imul r9, [ rsi + 0x38 ], 0x2
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, r9
mov [ rsp - 0x70 ], r12
mulx r12, r9, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r8
mov rdx, r13
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov rdi, rbx
mov [ rsp - 0x40 ], r13
xor r13, r13
adox rdi, rbx
mov [ rsp - 0x38 ], r12
mov r12, rbp
adox r12, rbp
xchg rdx, r8
mov [ rsp - 0x30 ], r9
mulx r9, r13, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r15
mov r15, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r14
lea r14, [r15 + r15]
mov r15, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], r9
lea r9, [r15 + r15]
xchg rdx, r9
mov [ rsp - 0x10 ], r13
mulx r13, r15, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], r15
mulx r15, r13, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rcx
mov rcx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r14
mov r14, rcx
shl r14, 0x1
xchg rdx, r14
mov [ rsp + 0x28 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r11
xor r11, r11
adox rbx, rax
mov [ rsp + 0x38 ], rcx
mov rcx, r10
adox rcx, rbp
mulx r11, rbp, [ rsi + 0x10 ]
adcx rbx, r13
mov [ rsp + 0x40 ], r11
mov r11, r15
adcx r11, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], rbx
mulx rbx, r11, r14
test al, al
adox rdi, rax
adox r10, r12
mov rdx, rcx
mulx rax, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rbx
mulx rbx, r12, r8
adcx rdi, r13
adcx r15, r10
mov rdx, r12
test al, al
adox rdx, [ rsp + 0x28 ]
mov r13, rbx
adox r13, [ rsp + 0x10 ]
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r11
mov [ rsp + 0x68 ], r15
mulx r15, r11, rdx
mov rdx, r10
adcx rdx, [ rsp + 0x28 ]
mov [ rsp + 0x70 ], rdi
mov rdi, r13
adcx rdi, [ rsp + 0x10 ]
test al, al
adox rdx, r12
adox rbx, rdi
adcx r10, r11
mov r12, r15
adcx r12, r13
add rdx, r11
adcx r15, rbx
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx rdi, r11, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], rax
mulx rax, rbx, [ rsp + 0x8 ]
xor rdx, rdx
adox r13, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
mov [ rsp + 0x80 ], rcx
mov rcx, r11
adcx rcx, [ rsp + 0x0 ]
adcx rdi, [ rsp - 0x8 ]
xor r11, r11
adox r13, [ rsp + 0x20 ]
adox r15, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rbp
mulx rbp, r11, r9
mov rdx, rcx
adcx rdx, rbx
adcx rax, rdi
add r10, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x18 ]
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], r12
mov [ rsp + 0x98 ], r10
mulx r10, r12, r14
mov rdx, r8
mov [ rsp + 0xa0 ], r10
mulx r10, r8, [ rsi + 0x30 ]
test al, al
adox rbx, r11
adox rbp, rax
mov r11, r8
adcx r11, [ rsp - 0x20 ]
mov rax, r10
adcx rax, [ rsp - 0x28 ]
mov [ rsp + 0xa8 ], rbp
mov rbp, r8
mov [ rsp + 0xb0 ], rbx
xor rbx, rbx
adox rbp, r8
adox r10, r10
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r10
mulx r10, rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], r12
mulx r12, rbp, r14
adcx r13, rbx
adcx r10, r15
mov rdx, [ rsi + 0x10 ]
lea r14, [rdx + rdx]
mov rdx, r14
mulx r15, r14, [ rsi + 0x8 ]
xor rbx, rbx
adox rcx, r14
adox r15, rdi
xchg rdx, r8
mulx r14, rdi, [ rsi + 0x8 ]
adcx r13, rdi
mov [ rsp + 0xd0 ], r15
mov r15, r14
adcx r15, r10
xor r10, r10
adox r11, rbp
mov rbx, r12
adox rbx, rax
adcx r11, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
mov rax, [ rsp + 0xb0 ]
mov [ rsp + 0xd8 ], rbx
xor rbx, rbx
adox rax, [ rsp + 0xc8 ]
mov r10, [ rsp + 0xa8 ]
adox r10, [ rsp + 0xa0 ]
mov [ rsp + 0xe0 ], r11
mulx r11, rbx, [ rsi + 0x0 ]
adcx rax, rbx
adcx r11, r10
mov rdx, [ rsp + 0xc0 ]
test al, al
adox rdx, [ rsp - 0x20 ]
mov r10, [ rsp + 0xb8 ]
adox r10, [ rsp - 0x28 ]
mov rbx, rax
shrd rbx, r11, 56
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r15
mulx r15, rbx, r8
xor rdx, rdx
adox r11, rbp
adox r12, r10
adcx r11, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, rdx
test al, al
adox r11, [ rsp + 0x88 ]
adox r12, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], r15
mulx r15, r10, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], rbx
lea rbx, [rdx + rdx]
mov rdx, r9
mov [ rsp + 0x108 ], r15
mulx r15, r9, [ rsi + 0x0 ]
adcx rcx, [ rsp + 0x80 ]
mov [ rsp + 0x110 ], r10
mov r10, [ rsp + 0x78 ]
adcx r10, [ rsp + 0xd0 ]
mov [ rsp + 0x118 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x120 ], rbp
mov [ rsp + 0x128 ], r15
mulx r15, rbp, rbx
mov rdx, rbp
add rdx, [ rsp + 0xe0 ]
adcx r15, [ rsp + 0xd8 ]
add r13, [ rsp + 0x38 ]
mov rbx, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0xf0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r15
mov [ rsp + 0x138 ], r9
mulx r9, r15, [ rsp + 0x8 ]
xor rdx, rdx
adox r13, r15
adox r9, rbx
mov rdx, [ rsi + 0x8 ]
mulx r15, rbx, [ rsp + 0x8 ]
mov rdx, rcx
shrd rdx, r10, 56
xor r10, r10
adox r13, rdx
adox r9, r10
mov rdx, [ rsp + 0x98 ]
adcx rdx, [ rsp + 0x20 ]
mov [ rsp + 0x140 ], rbp
mov rbp, [ rsp + 0x90 ]
adcx rbp, [ rsp + 0x18 ]
mov [ rsp + 0x148 ], r12
mov r12, r13
test al, al
adox r12, [ rsp + 0xe8 ]
adox r9, r10
xchg rdx, r8
mulx r10, r13, [ rsi + 0x8 ]
adcx r8, rdi
adcx r14, rbp
xor rdx, rdx
adox r11, rbx
adox r15, [ rsp + 0x148 ]
mov rdi, [ rsp - 0x40 ]
mov rbx, rdi
adcx rbx, [ rsp + 0x70 ]
mov rbp, [ rsp - 0x48 ]
mov [ rsp + 0x150 ], r14
mov r14, rbp
adcx r14, [ rsp + 0x68 ]
mov [ rsp + 0x158 ], r8
xor r8, r8
adox r11, [ rsp + 0x138 ]
adox r15, [ rsp + 0x128 ]
adcx rbx, [ rsp + 0x120 ]
adcx r14, [ rsp + 0x118 ]
mov rdx, r12
shrd rdx, r9, 56
xor r9, r9
adox r11, rdx
adox r15, r9
adcx rbx, [ rsp + 0x110 ]
adcx r14, [ rsp + 0x108 ]
xor r8, r8
adox rbx, r13
adox r10, r14
mov rdx, [ rsi + 0x0 ]
mulx r13, r9, rdx
mov rdx, r9
adcx rdx, [ rsp + 0x158 ]
adcx r13, [ rsp + 0x150 ]
mov r14, rdx
add r14, [ rsp + 0xe8 ]
adc r13, 0x0
mov r9, 0x38 
bzhi rdx, r11, r9
mov r8, r14
shrd r8, r13, 56
xor r13, r13
adox rbx, [ rsp + 0x60 ]
adox r10, [ rsp + 0x58 ]
shrd r11, r15, 56
xor r15, r15
adox rbx, r11
adox r10, r15
mov r13, r8
adcx r13, [ rsp + 0x140 ]
mov r11, [ rsp + 0x130 ]
adc r11, 0x0
mov r8, rbx
shrd r8, r10, 56
bzhi r15, rbx, r9
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x30 ], r15
bzhi r10, rax, r9
lea r8, [ r8 + r10 ]
bzhi rax, r8, r9
mov r15, r13
shrd r15, r11, 56
bzhi r11, r12, r9
shr r8, 56
bzhi r12, r14, r9
lea r11, [ r11 + r8 ]
lea r12, [ r12 + r8 ]
mov r14, rdi
adox r14, [ rsp + 0x50 ]
adox rbp, [ rsp + 0x48 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, r10, rdx
bzhi rdx, r13, r9
adox r14, r10
adox r8, rbp
mov r13, r12
shr r13, 56
bzhi rbp, rcx, r9
adox r14, [ rsp + 0x100 ]
adox r8, [ rsp + 0xf8 ]
add r14, r15
adc r8, 0x0
mov rcx, r14
shrd rcx, r8, 56
lea rcx, [ rcx + rbp ]
mov r15, rcx
shr r15, 56
lea r15, [ r15 + r11 ]
bzhi r11, rcx, r9
mov [ rbx + 0x18 ], r11
bzhi r10, r15, r9
lea r13, [ r13 + rdx ]
shr r15, 56
mov [ rbx + 0x20 ], r10
mov [ rbx + 0x8 ], r13
bzhi rdx, r12, r9
mov [ rbx + 0x0 ], rdx
bzhi r12, r14, r9
mov [ rbx + 0x10 ], r12
lea r15, [ r15 + rdi ]
mov [ rbx + 0x38 ], rax
mov [ rbx + 0x28 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 480
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0474
; seed 3855529194171405 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3238238 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=127, initial num_batches=31): 110954 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03426369525649443
; number reverted permutation / tried permutation: 63076 / 89993 =70.090%
; number reverted decision / tried decision: 49981 / 90006 =55.531%
; validated in 1.697s
