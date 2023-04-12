SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 424
mov rax, 0x1 
shlx r10, [ rsi + 0x38 ], rax
mov rdx, [ rsi + 0x30 ]
mulx rcx, r11, r10
imul rdx, [ rsi + 0x20 ], 0x2
mulx r9, r8, [ rsi + 0x8 ]
xchg rdx, r10
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, 0x1 
mov [ rsp - 0x70 ], r12
shlx r12, [ rsi + 0x30 ], rbp
imul rbp, [ rsi + 0x28 ], 0x2
xchg rdx, r12
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r9
mulx r9, r13, rdx
mov rdx, rbp
mov [ rsp - 0x30 ], r8
mulx r8, rbp, [ rsi + 0x10 ]
xchg rdx, r14
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r8
mov r8, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbp
lea rbp, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r13
mulx r13, r9, r12
imul rdx, [ rsi + 0x10 ], 0x2
xchg rdx, r10
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r10
mulx r10, rbp, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r13
mulx r13, rbp, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], rbp
mulx rbp, r13, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], r13
mulx r13, rbp, r14
mov rdx, r11
mov [ rsp + 0x50 ], r9
xor r9, r9
adox rdx, rbp
mov [ rsp + 0x58 ], r15
mov r15, r13
adox r15, rcx
mov [ rsp + 0x60 ], rdi
mov rdi, r11
adcx rdi, r11
adcx rcx, rcx
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rbx
mulx rbx, r9, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], rax
mov [ rsp + 0x78 ], r15
mulx r15, rax, rdx
xor rdx, rdx
adox rdi, rbp
adox r13, rcx
adcx rdi, r9
mov rbp, rbx
adcx rbp, r13
mov rdx, r10
mulx rcx, r10, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r9
adox rbx, [ rsp + 0x78 ]
adcx rdi, [ rsp + 0x70 ]
adcx rbp, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, r9, rdx
mov rdx, r12
mov [ rsp + 0x80 ], rbx
mulx rbx, r12, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r11
mov r11, rax
test al, al
adox r11, r12
mov [ rsp + 0x90 ], rcx
mov rcx, rbx
adox rcx, r15
mov [ rsp + 0x98 ], r10
mov r10, r11
adcx r10, rax
adcx r15, rcx
xchg rdx, r14
mov [ rsp + 0xa0 ], rbp
mulx rbp, rax, [ rsi + 0x18 ]
mov [ rsp + 0xa8 ], rdi
xor rdi, rdi
adox r10, r12
adox rbx, r15
adcx r11, r9
mov r12, r13
adcx r12, rcx
xor rcx, rcx
adox r10, r9
adox r13, rbx
xchg rdx, r8
mulx r9, rdi, [ rsi + 0x28 ]
adcx r10, rax
mov r15, rbp
adcx r15, r13
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mulx rcx, r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], r12
mov [ rsp + 0xb8 ], r11
mulx r11, r12, rdx
test al, al
adox r10, [ rsp + 0x60 ]
adox r15, [ rsp + 0x58 ]
mov rdx, r13
adcx rdx, r12
mov [ rsp + 0xc0 ], r15
mov r15, r11
adcx r15, rcx
mov [ rsp + 0xc8 ], r10
mov r10, r13
test al, al
adox r10, r13
adox rcx, rcx
xchg rdx, r14
mov [ rsp + 0xd0 ], r15
mulx r15, r13, [ rsi + 0x20 ]
adcx rdi, r13
adcx r15, r9
xor r9, r9
adox r10, r12
adox r11, rcx
mov r12, rax
adcx r12, [ rsp + 0xb8 ]
adcx rbp, [ rsp + 0xb0 ]
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, rcx, rdx
test al, al
adox r12, [ rsp + 0x60 ]
adox rbp, [ rsp + 0x58 ]
mov rdx, rbx
mulx r9, rbx, [ rsi + 0x20 ]
adcx r10, rbx
mov rdx, r9
adcx rdx, r11
test al, al
adox r10, [ rsp + 0x50 ]
adox rdx, [ rsp + 0x28 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], r12
mulx r12, rbp, [ rsp + 0x10 ]
adcx r10, rcx
adcx r13, r11
xor rdx, rdx
adox r14, rbx
adox r9, [ rsp + 0xd0 ]
mov rcx, rdi
adcx rcx, rbp
adcx r12, r15
xor rbx, rbx
adox r14, [ rsp + 0x50 ]
adox r9, [ rsp + 0x28 ]
adcx rdi, [ rsp + 0x20 ]
adcx r15, [ rsp + 0x18 ]
mov rdx, rax
mulx r11, rax, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x8 ]
mulx rbx, rbp, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], r14
mulx r14, r9, [ rsi + 0x8 ]
test al, al
adox rcx, rbp
adox rbx, r12
mov r12, [ rsp + 0x0 ]
mov rbp, r12
adcx rbp, [ rsp + 0xc8 ]
mov [ rsp + 0xf8 ], r13
mov r13, [ rsp - 0x8 ]
adcx r13, [ rsp + 0xc0 ]
test al, al
adox rbp, rax
mov r12, r11
adox r12, r13
adcx rdi, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x18 ]
test al, al
adox rbp, r9
adox r14, r12
adcx rdi, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
xor r9, r9
adox rbp, [ rsp + 0x48 ]
adox r14, [ rsp + 0x40 ]
mulx r12, r13, [ rsi + 0x10 ]
mov rdx, 0x38 
bzhi r9, rcx, rdx
mov rdx, r13
adox rdx, [ rsp + 0xa8 ]
adox r12, [ rsp + 0xa0 ]
shrd rcx, rbx, 56
test al, al
adox r10, [ rsp + 0x98 ]
mov rbx, [ rsp + 0x90 ]
adox rbx, [ rsp + 0xf8 ]
adcx rbp, rcx
adc r14, 0x0
test al, al
adox rdi, [ rsp + 0x38 ]
adox r15, [ rsp + 0x30 ]
mov r13, rdi
shrd r13, r15, 56
xchg rdx, r8
mulx r15, rcx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r9
mov r9, r13
mov [ rsp + 0x108 ], rbx
xor rbx, rbx
adox r9, rbp
adox r14, rbx
adcx r8, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
mov rbp, r9
shrd rbp, r14, 56
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], r10
mulx r10, rbx, rdx
mov rdx, r14
mov [ rsp + 0x118 ], r10
mulx r10, r14, [ rsi + 0x0 ]
add r8, r14
adcx r10, r12
xor rdx, rdx
adox r8, rbp
adox r10, rdx
mov r12, 0xffffffffffffff 
and r9, r12
mov rbp, rcx
adox rbp, [ rsp + 0x110 ]
adox r15, [ rsp + 0x108 ]
mov rcx, r8
shrd rcx, r10, 56
test al, al
adox rbp, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
adcx rbp, rcx
adc r15, 0x0
mov r14, rax
xor r10, r10
adox r14, [ rsp + 0xe0 ]
adox r11, [ rsp + 0xd8 ]
adcx r14, rbx
adcx r11, [ rsp + 0x118 ]
test al, al
adox r13, r14
adox r11, r10
mov rdx, rbp
and rdx, r12
mov rax, 0x1 
shlx rbx, [ rsi + 0x8 ], rax
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x30 ], rdx
mov rdx, rbx
mulx r14, rbx, [ rsi + 0x0 ]
mov rdx, r13
shrd rdx, r11, 56
mov r11, [ rsp + 0x88 ]
test al, al
adox r11, [ rsp + 0x70 ]
mov rax, [ rsp + 0x80 ]
adox rax, [ rsp + 0x68 ]
mov r10, rdx
mov rdx, [ rsp + 0x10 ]
mulx rcx, r12, [ rsi + 0x0 ]
mov rdx, 0x38 
mov [ rsp + 0x120 ], r9
bzhi r9, rdi, rdx
adox r11, rbx
adox r14, rax
shrd rbp, r15, 56
test al, al
adox r11, r10
mov rdi, 0x0 
adox r14, rdi
mov rdx, [ rsi + 0x8 ]
mulx rbx, r15, rdx
lea rbp, [ rbp + r9 ]
mov rdx, r15
adcx rdx, [ rsp + 0xf0 ]
adcx rbx, [ rsp + 0xe8 ]
add rdx, r12
adcx rcx, rbx
mov r10, rbp
shr r10, 56
mov rax, 0x38 
bzhi r12, r13, rax
mov r13, r11
shrd r13, r14, 56
lea r12, [ r12 + r10 ]
xor r9, r9
adox rdx, r13
adox rcx, r9
mov rdi, rdx
shrd rdi, rcx, 56
bzhi r14, r12, rax
bzhi r15, rbp, rax
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x38 ], r15
bzhi rbx, r11, rax
shr r12, 56
add rdi, [ rsp + 0x100 ]
lea r12, [ r12 + rbx ]
mov r11, rdi
shr r11, 56
add r10, [ rsp + 0x120 ]
lea r11, [ r11 + r10 ]
mov r13, r11
shr r13, 56
bzhi rcx, r8, rax
lea r13, [ r13 + rcx ]
bzhi r8, rdi, rax
bzhi r15, rdx, rax
mov [ rbp + 0x18 ], r8
bzhi rdx, r11, rax
mov [ rbp + 0x20 ], rdx
mov [ rbp + 0x0 ], r14
mov [ rbp + 0x28 ], r13
mov [ rbp + 0x8 ], r12
mov [ rbp + 0x10 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 424
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0537
; seed 0614998047658479 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2580479 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=119, initial num_batches=31): 88676 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03436416262252086
; number reverted permutation / tried permutation: 63867 / 90274 =70.748%
; number reverted decision / tried decision: 53922 / 89725 =60.097%
; validated in 1.158s
