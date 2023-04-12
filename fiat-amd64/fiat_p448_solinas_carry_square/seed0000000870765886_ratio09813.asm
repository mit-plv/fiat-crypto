SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 512
imul rax, [ rsi + 0x28 ], 0x2
mov r10, 0x1 
shlx r11, [ rsi + 0x30 ], r10
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x38 ]
lea r9, [rdx + rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, rdx
imul rdx, [ rsi + 0x8 ], 0x2
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r9
mov rdx, r9
mov [ rsp - 0x60 ], r14
mulx r14, r9, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r13
mulx r13, r12, r15
mov rdx, r11
mov [ rsp - 0x18 ], r13
mulx r13, r11, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], r12
mulx r12, r11, rax
mov rdx, r15
mov [ rsp + 0x8 ], r12
mulx r12, r15, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r12
mulx r12, r11, [ rsi + 0x30 ]
mov [ rsp + 0x20 ], r15
mov r15, r11
mov [ rsp + 0x28 ], r8
xor r8, r8
adox r15, r11
mov [ rsp + 0x30 ], rcx
mov rcx, r12
adox rcx, r12
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r15
mulx r15, rcx, r13
mov rdx, rax
mov [ rsp + 0x48 ], rbx
mulx rbx, rax, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], rax
mov [ rsp + 0x60 ], r10
mulx r10, rax, r8
mov rdx, rbx
mov [ rsp + 0x68 ], r14
mulx r14, rbx, [ rsi + 0x20 ]
adcx rdi, rax
adcx r10, rbp
test al, al
adox r11, rbx
mov rbp, r14
adox rbp, r12
mov r12, 0x1 
shlx rax, [ rsi + 0x20 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r9
mov [ rsp + 0x78 ], r10
mulx r10, r9, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r10
mov [ rsp + 0x88 ], r9
mulx r9, r10, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r9
mulx r9, rdi, r8
mov rdx, [ rsi + 0x10 ]
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], r9
mov [ rsp + 0xa8 ], rdi
mulx rdi, r9, r8
adcx r11, rcx
mov rdx, r15
adcx rdx, rbp
mov rbp, r10
mov [ rsp + 0xb0 ], rdi
xor rdi, rdi
adox rbp, [ rsp + 0x90 ]
mov [ rsp + 0xb8 ], r9
mov r9, [ rsp + 0x98 ]
adox r9, [ rsp + 0x78 ]
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r11
mulx r11, rdi, r13
mov rdx, r8
mov [ rsp + 0xc8 ], r10
mulx r10, r8, [ rsi + 0x8 ]
mov rdx, r8
adcx rdx, [ rsp + 0x90 ]
adcx r10, [ rsp + 0x78 ]
mov r8, [ rsp + 0x70 ]
mov [ rsp + 0xd0 ], r10
mov r10, r8
mov [ rsp + 0xd8 ], rdx
xor rdx, rdx
adox r10, [ rsp + 0x60 ]
mov [ rsp + 0xe0 ], r11
mov r11, [ rsp + 0x68 ]
mov [ rsp + 0xe8 ], rdi
mov rdi, r11
adox rdi, [ rsp + 0x48 ]
mov [ rsp + 0xf0 ], r9
mov r9, r10
adcx r9, [ rsp + 0x30 ]
mov [ rsp + 0xf8 ], rbp
mov rbp, rdi
adcx rbp, [ rsp + 0x28 ]
mov [ rsp + 0x100 ], rbp
mov rbp, rbx
test al, al
adox rbp, [ rsp + 0x40 ]
adox r14, [ rsp + 0x38 ]
adcx r10, [ rsp + 0x60 ]
adcx rdi, [ rsp + 0x48 ]
xor rbx, rbx
adox r10, r8
adox r11, rdi
adcx rbp, rcx
adcx r15, r14
xor rdx, rdx
adox r10, [ rsp + 0x30 ]
adox r11, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rbx, r12
mov rdx, [ rsi + 0x38 ]
mulx r14, rcx, rdx
mov rdx, rbx
adcx rdx, [ rsp + 0xf8 ]
adcx r8, [ rsp + 0xf0 ]
add rdx, [ rsp + 0xe8 ]
adcx r8, [ rsp + 0xe0 ]
xchg rdx, r13
mulx rbx, rdi, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], rbx
mulx rbx, rbp, r12
add r13, [ rsp - 0x30 ]
adcx r8, [ rsp - 0x40 ]
add r9, rbp
mov rdx, rbx
adcx rdx, [ rsp + 0x100 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r9
mov [ rsp + 0x128 ], rdi
mulx rdi, r9, rdx
mov rdx, r15
mov [ rsp + 0x130 ], r12
mulx r12, r15, [ rsi + 0x10 ]
add r10, rbp
adcx rbx, r11
add r10, r15
mov rdx, r12
adcx rdx, rbx
mov r11, rcx
xor rbp, rbp
adox r11, [ rsp - 0x20 ]
mov rbx, r14
adox rbx, [ rsp - 0x28 ]
mov rbp, 0xffffffffffffff 
mov [ rsp + 0x138 ], rbx
mov rbx, r13
and rbx, rbp
adox r10, r9
adox rdi, rdx
mov r9, rcx
adcx r9, rcx
adcx r14, r14
add r9, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
xor rcx, rcx
adox r9, [ rsp + 0x128 ]
adox r14, [ rsp + 0x118 ]
adcx r11, [ rsp + 0x128 ]
mov rdx, [ rsp + 0x118 ]
adcx rdx, [ rsp + 0x138 ]
test al, al
adox r10, [ rsp + 0x20 ]
adox rdi, [ rsp + 0x18 ]
adcx r11, [ rsp + 0xa8 ]
adcx rdx, [ rsp + 0xa0 ]
mov rcx, rdx
mov rdx, [ rsp - 0x38 ]
mov [ rsp + 0x140 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov [ rsp + 0x148 ], rcx
mov rcx, rbp
mov [ rsp + 0x150 ], r11
xor r11, r11
adox rcx, [ rsp + 0xd8 ]
adox rbx, [ rsp + 0xd0 ]
shrd r13, r8, 56
mov r8, rcx
shrd r8, rbx, 56
xor rbp, rbp
adox r9, [ rsp + 0xa8 ]
adox r14, [ rsp + 0xa0 ]
mulx rbx, r11, [ rsi + 0x8 ]
adcx r10, r11
adcx rbx, rdi
mov rdi, r15
test al, al
adox rdi, [ rsp + 0x120 ]
adox r12, [ rsp + 0x130 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r11, rax
adcx r10, r11
adcx rbp, rbx
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, rdx
xor rdx, rdx
adox rdi, [ rsp + 0x20 ]
adox r12, [ rsp + 0x18 ]
adcx rdi, rbx
adcx r11, r12
mov rdx, r15
mulx rbx, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, r8
adox rbp, rdx
mov r8, r13
adcx r8, rdi
adc r11, 0x0
test al, al
adox r13, r10
adox rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r12, rdx
mov rdx, [ rsp + 0xc0 ]
adcx rdx, [ rsp + 0x0 ]
mov r10, [ rsp + 0xc8 ]
adcx r10, [ rsp - 0x18 ]
mov [ rsp + 0x158 ], r14
mov r14, 0x38 
mov [ rsp + 0x160 ], r9
bzhi r9, r13, r14
shrd r13, rbp, 56
mov rbp, [ rsp + 0x110 ]
xor r14, r14
adox rbp, [ rsp + 0x0 ]
mov [ rsp + 0x168 ], r9
mov r9, [ rsp + 0x108 ]
adox r9, [ rsp - 0x18 ]
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], r13
mov [ rsp + 0x178 ], rdi
mulx rdi, r13, rax
adcx rbp, r15
adcx rbx, r9
mov rdx, [ rsi + 0x0 ]
mulx r15, rax, [ rsp - 0x48 ]
add r14, rax
adcx r15, r10
mov rdx, r8
shrd rdx, r11, 56
xor r11, r11
adox r14, rdx
adox r15, r11
mov r10, r12
adcx r10, [ rsp + 0x160 ]
mov r9, [ rsp + 0x178 ]
adcx r9, [ rsp + 0x158 ]
mov r12, r14
shrd r12, r15, 56
test al, al
adox r10, [ rsp + 0x88 ]
adox r9, [ rsp + 0x80 ]
adcx rbp, r13
adcx rdi, rbx
test al, al
adox rbp, [ rsp + 0x10 ]
adox rdi, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, rdx
mov rdx, r13
adcx rdx, [ rsp + 0x150 ]
adcx rbx, [ rsp + 0x148 ]
xor rax, rax
adox rbp, [ rsp + 0x170 ]
adox rdi, rax
mov r11, 0x38 
bzhi r15, rbp, r11
shrd rbp, rdi, 56
xor r13, r13
adox r10, [ rsp + 0x58 ]
adox r9, [ rsp + 0x50 ]
adcx r10, [ rsp - 0x8 ]
adcx r9, [ rsp - 0x10 ]
xor rax, rax
adox rdx, [ rsp + 0xb8 ]
adox rbx, [ rsp + 0xb0 ]
adcx rdx, r12
adc rbx, 0x0
test al, al
adox r10, rbp
adox r9, rax
mov r13, rdx
shrd r13, rbx, 56
bzhi r12, rcx, r11
bzhi rcx, rdx, r11
mov rdi, r10
shrd rdi, r9, 56
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], rcx
bzhi rdx, r10, r11
add rdi, [ rsp + 0x140 ]
mov rbx, rdi
shr rbx, 56
bzhi r10, rdi, r11
bzhi r9, r8, r11
lea r9, [ r9 + rbx ]
lea r13, [ r13 + r12 ]
mov [ rbp + 0x38 ], r10
add rbx, [ rsp + 0x168 ]
mov r8, r13
shr r8, 56
lea r8, [ r8 + rbx ]
bzhi r12, r8, r11
shr r8, 56
mov rcx, r9
shr rcx, 56
bzhi rdi, r14, r11
lea rcx, [ rcx + rdi ]
lea r8, [ r8 + r15 ]
mov [ rbp + 0x20 ], r12
mov [ rbp + 0x28 ], r8
mov [ rbp + 0x8 ], rcx
bzhi r14, r9, r11
mov [ rbp + 0x30 ], rdx
bzhi r15, r13, r11
mov [ rbp + 0x0 ], r14
mov [ rbp + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 512
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9813
; seed 0209616856035182 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5271112 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=80, initial num_batches=31): 179561 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.034065108083455635
; number reverted permutation / tried permutation: 60406 / 90177 =66.986%
; number reverted decision / tried decision: 45643 / 89822 =50.815%
; validated in 2.31s
