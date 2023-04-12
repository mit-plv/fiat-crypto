SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 360
mov rax, 0x1 
shlx r10, [ rsi + 0x38 ], rax
imul r11, [ rsi + 0x10 ], 0x2
imul rdx, [ rsi + 0x18 ], 0x2
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, r10
mov [ rsp - 0x68 ], r13
mulx r13, r10, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov r14, 0x1 
mov [ rsp - 0x58 ], r15
shlx r15, [ rsi + 0x30 ], r14
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
xchg rdx, r15
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rax
mulx rax, rbx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r9
mov r9, r10
add r9, r10
mov [ rsp - 0x30 ], r8
mov r8, r13
adcx r8, r13
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
test al, al
adox rbx, rbp
adox r12, rax
mulx rax, rbp, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rax
mov [ rsp + 0x0 ], rbp
mulx rbp, rax, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x10 ], rax
mov [ rsp + 0x18 ], r12
mulx r12, rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], r14
mulx r14, rbx, rdx
mov rdx, rax
adcx rdx, rbx
mov [ rsp + 0x30 ], r11
mov r11, r14
adcx r11, r12
mov [ rsp + 0x38 ], r11
mov r11, 0x1 
mov [ rsp + 0x40 ], rdx
shlx rdx, [ rsi + 0x28 ], r11
mov r11, rax
test al, al
adox r11, rax
adox r12, r12
adcx r11, rbx
adcx r14, r12
mulx rbx, rax, [ rsi + 0x20 ]
mov r12, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r14
mov r14, r12
shl r14, 0x1
xor r12, r12
adox r9, rax
mov [ rsp + 0x50 ], r14
mov r14, rbx
adox r14, r8
adcx r10, rax
adcx rbx, r13
mulx r8, r13, [ rsi + 0x8 ]
xor rax, rax
adox r9, rdi
adox r14, [ rsp + 0x30 ]
xchg rdx, rcx
mulx rax, r12, [ rsi + 0x0 ]
adcx r9, [ rsp + 0x28 ]
adcx r14, [ rsp - 0x20 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r13
mulx r13, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r8
adox r13, r14
mov rdx, rbp
mulx r14, rbp, [ rsi + 0x20 ]
adcx r10, rdi
adcx rbx, [ rsp + 0x30 ]
xor rdx, rdx
adox r11, rbp
mov rdi, r14
adox rdi, [ rsp + 0x48 ]
adcx r10, [ rsp + 0x28 ]
adcx rbx, [ rsp - 0x20 ]
mov r8, rbp
test al, al
adox r8, [ rsp + 0x40 ]
adox r14, [ rsp + 0x38 ]
mov rdx, r15
mulx rbp, r15, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x80 ], r9
mov [ rsp + 0x88 ], rax
mulx rax, r9, rdx
adcx r8, rbx
mov rdx, r10
adcx rdx, r14
xor r14, r14
adox r11, rbx
adox r10, rdi
mov rdi, r9
adcx rdi, r15
mov rbx, rbp
adcx rbx, rax
mov [ rsp + 0x90 ], r10
mov r10, rdi
mov [ rsp + 0x98 ], r11
xor r11, r11
adox r10, r9
adox rax, rbx
adcx r10, r15
adcx rbp, rax
mov r14, [ rsi + 0x20 ]
lea r15, [r14 + r14]
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r9, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], r14
mulx r14, r11, [ rsp - 0x28 ]
mov rdx, r9
add rdx, [ rsp + 0x20 ]
adcx rax, [ rsp + 0x18 ]
mov r9, r11
add r9, [ rsp + 0x20 ]
adcx r14, [ rsp + 0x18 ]
xor r11, r11
adox r9, r12
adox r14, [ rsp + 0x88 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r8
mulx r8, r11, rcx
adcx r12, r11
adcx r8, rax
mov rdx, 0x38 
bzhi rax, r9, rdx
adox r12, [ rsp + 0x10 ]
adox r8, [ rsp + 0x8 ]
shrd r9, r14, 56
mov rdx, [ rsi + 0x0 ]
mulx r11, r14, r13
mov rdx, r13
mov [ rsp + 0xb0 ], rax
mulx rax, r13, [ rsi + 0x8 ]
mov rdx, rcx
mov [ rsp + 0xb8 ], r9
mulx r9, rcx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], rax
xor rax, rax
adox r12, r14
adox r11, r8
adcx rdi, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
mov r8, r12
shrd r8, r11, 56
add rdi, rcx
mov r14, r9
adcx r14, rbx
mov rbx, 0x38 
bzhi rax, r12, rbx
adox r10, [ rsp - 0x30 ]
adox rbp, [ rsp - 0x38 ]
test al, al
adox rdi, [ rsp + 0x0 ]
adox r14, [ rsp - 0x8 ]
adcx r10, rcx
adcx r9, rbp
add r10, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, rbp, rdx
xor rdx, rdx
adox r10, rbp
adox rbx, r9
mov rdx, r15
mulx r9, r15, [ rsi + 0x0 ]
adcx r10, r13
adcx rbx, [ rsp + 0xc0 ]
test al, al
adox r10, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
adcx rdi, r13
adcx r14, [ rsp + 0xc0 ]
test al, al
adox r10, r15
adox r9, rbx
adcx rdi, r12
adcx r11, r14
mulx r12, r13, [ rsi + 0x8 ]
mov rbp, r13
xor r15, r15
adox rbp, [ rsp + 0x80 ]
adox r12, [ rsp + 0x78 ]
adcx r10, [ rsp + 0xb8 ]
adc r9, 0x0
mov rbx, r8
xor r14, r14
adox rbx, r10
adox r9, r14
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r13, rdx
mov rdx, 0x38 
bzhi r14, rbx, rdx
mov rdx, rcx
mov [ rsp + 0xc8 ], r14
mulx r14, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], rax
mov [ rsp + 0xd8 ], r11
mulx r11, rax, rdx
adox rbp, rcx
adox r14, r12
mov rdx, [ rsi + 0x0 ]
mulx rcx, r12, [ rsp - 0x28 ]
shrd rbx, r9, 56
mov rdx, r13
xor r9, r9
adox rdx, [ rsp + 0xa8 ]
adox r10, [ rsp + 0xa0 ]
adcx rbp, rbx
adc r14, 0x0
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, rbx, [ rsp + 0x50 ]
mov rdx, rbp
shrd rdx, r14, 56
mov r14, rbx
mov [ rsp + 0xe0 ], rdx
xor rdx, rdx
adox r14, [ rsp + 0x70 ]
adox r9, [ rsp + 0x68 ]
adcx r8, rdi
mov rbx, [ rsp + 0xd8 ]
adc rbx, 0x0
test al, al
adox r13, r12
adox rcx, r10
mov rdi, r8
shrd rdi, rbx, 56
xor r12, r12
adox r14, rdi
adox r9, r12
mov rdx, r14
shrd rdx, r9, 56
mov r10, rax
add r10, [ rsp + 0x98 ]
adcx r11, [ rsp + 0x90 ]
mov rax, 0x38 
bzhi rbx, r14, rax
adox r13, rdx
adox rcx, r12
mov rdi, r13
shrd rdi, rcx, 56
add rdi, [ rsp + 0xb0 ]
bzhi r14, r13, rax
mov rdx, r15
mulx r9, r15, [ rsi + 0x10 ]
adox r10, r15
adox r9, r11
mov rdx, rdi
shr rdx, 56
add r10, [ rsp + 0x60 ]
adcx r9, [ rsp + 0x58 ]
xor r11, r11
adox r10, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
adcx r10, [ rsp + 0xe0 ]
adc r9, 0x0
bzhi r12, r10, rax
bzhi r13, rdi, rax
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], r13
shrd r10, r9, 56
add r10, [ rsp + 0xd0 ]
mov rdi, r10
shr rdi, 56
bzhi r15, r10, rax
bzhi r9, r8, rax
lea r9, [ r9 + rdi ]
mov r8, r9
shr r8, 56
add rdi, [ rsp + 0xc8 ]
lea rdx, [ rdx + rdi ]
lea r8, [ r8 + rbx ]
bzhi rbx, rbp, rax
mov rbp, rdx
shr rbp, 56
lea rbp, [ rbp + rbx ]
mov [ rcx + 0x28 ], rbp
bzhi r13, r9, rax
mov [ rcx + 0x30 ], r12
mov [ rcx + 0x10 ], r14
bzhi r14, rdx, rax
mov [ rcx + 0x38 ], r15
mov [ rcx + 0x20 ], r14
mov [ rcx + 0x0 ], r13
mov [ rcx + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 360
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0678
; seed 0493819125725610 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5353272 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=107, initial num_batches=31): 174138 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0325292643452453
; number reverted permutation / tried permutation: 65932 / 90066 =73.204%
; number reverted decision / tried decision: 60240 / 89933 =66.983%
; validated in 1.795s
