SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 456
mov rax, [ rsi + 0x10 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x28 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
mov rdx, 0x1 
shlx r9, [ rsi + 0x28 ], rdx
imul rdx, [ rsi + 0x20 ], 0x2
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
shl r15, 0x1
mov rdx, rbx
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r15
imul r15, [ rsi + 0x30 ], 0x2
mov [ rsp - 0x40 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rdi
mulx rdi, r13, r15
mov rdx, 0x1 
mov [ rsp - 0x28 ], rbx
shlx rbx, [ rsi + 0x18 ], rdx
mov rdx, r15
mov [ rsp - 0x20 ], rbx
mulx rbx, r15, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r8
mulx r8, r13, r9
mov rdx, r9
mov [ rsp + 0x0 ], r8
mulx r8, r9, [ rsi + 0x20 ]
xchg rdx, rdi
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r9
mulx r9, r8, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], r13
mulx r13, r8, r10
mov rdx, r9
mov [ rsp + 0x30 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
xchg rdx, r10
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], r8
mulx r8, r13, [ rsi + 0x0 ]
mov rdx, rbp
add rdx, rax
mov [ rsp + 0x48 ], r8
mov r8, r11
adcx r8, r12
mov [ rsp + 0x50 ], r13
mov r13, [ rsi + 0x38 ]
mov [ rsp + 0x58 ], rbx
lea rbx, [r13 + r13]
test al, al
adox rdx, r9
mov r13, rcx
adox r13, r8
mov r8, rbp
adcx r8, rbp
adcx r12, r12
xchg rdx, rbx
mov [ rsp + 0x60 ], r13
mulx r13, rbp, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r13
mulx r13, rbx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rbp
mov [ rsp + 0x80 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], rbp
xor rbp, rbp
adox r15, rbx
adox r13, [ rsp + 0x58 ]
xchg rdx, r10
mulx rbp, rbx, [ rsi + 0x10 ]
adcx r8, rax
adcx r11, [ rsp + 0x80 ]
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r12
mov [ rsp + 0xc8 ], rbp
mulx rbp, r12, r10
xor rdx, rdx
adox r8, r9
adox rcx, r11
mov rdx, [ rsi + 0x30 ]
mulx r10, r9, rdx
mov rdx, r15
adcx rdx, [ rsp + 0x40 ]
mov r11, r13
adcx r11, [ rsp + 0x38 ]
mov [ rsp + 0xd0 ], r11
mov r11, r9
test al, al
adox r11, r12
mov [ rsp + 0xd8 ], rdx
mov rdx, rbp
adox rdx, r10
adcx r8, [ rsp + 0xa0 ]
adcx rcx, [ rsp + 0x98 ]
mov [ rsp + 0xe0 ], rcx
mov rcx, r11
mov [ rsp + 0xe8 ], r8
xor r8, r8
adox rcx, [ rsp + 0x30 ]
mov [ rsp + 0xf0 ], rbx
mov rbx, rdx
adox rbx, [ rsp - 0x8 ]
adcx r11, r9
adcx r10, rdx
test al, al
adox r11, r12
adox rbp, r10
adcx rcx, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x0 ]
mov r12, [ rsp + 0x78 ]
mov r9, r12
xor rdx, rdx
adox r9, r12
mov r8, [ rsp + 0x70 ]
mov r10, r8
adox r10, r8
adcx rcx, [ rsp + 0xf0 ]
adcx rbx, [ rsp + 0xc8 ]
test al, al
adox r9, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
adcx r9, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
mov [ rsp + 0xf8 ], r10
xor r10, r10
adox r12, [ rsp + 0x10 ]
adox r8, [ rsp + 0x8 ]
adcx r12, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
add rcx, [ rsp + 0x90 ]
adcx rbx, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r8
mulx r8, r10, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x108 ], r12
mov [ rsp + 0x110 ], rbx
mulx rbx, r12, r14
add r15, r12
adcx rbx, r13
xor rdx, rdx
adox r11, [ rsp + 0x30 ]
adox rbp, [ rsp - 0x8 ]
adcx r11, [ rsp + 0x28 ]
adcx rbp, [ rsp + 0x0 ]
mov rdx, rdi
mulx r13, rdi, [ rsi + 0x10 ]
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], rcx
mov [ rsp + 0x120 ], r9
mulx r9, rcx, rdx
add r15, rdi
adcx r13, rbx
mov rdx, r10
test al, al
adox rdx, [ rsp + 0xd8 ]
adox r8, [ rsp + 0xd0 ]
adcx r11, [ rsp + 0xf0 ]
adcx rbp, [ rsp + 0xc8 ]
xchg rdx, rax
mulx rbx, r10, [ rsi + 0x8 ]
add r15, r10
adcx rbx, r13
test al, al
adox r11, rcx
adox r9, rbp
adcx r15, [ rsp + 0xb0 ]
adcx rbx, [ rsp + 0xa8 ]
mov rdx, 0xffffffffffffff 
mov rdi, r15
and rdi, rdx
mov rdx, [ rsp - 0x20 ]
mulx r13, rcx, [ rsi + 0x8 ]
adox r11, [ rsp + 0x90 ]
adox r9, [ rsp + 0x88 ]
shrd r15, rbx, 56
xchg rdx, r14
mulx r10, rbp, [ rsi + 0x8 ]
mov rbx, rax
shrd rbx, r8, 56
add r11, rcx
adcx r13, r9
mov r8, [ rsp + 0x120 ]
add r8, [ rsp + 0xc0 ]
mov rcx, [ rsp + 0xf8 ]
adcx rcx, [ rsp + 0xb8 ]
add r11, [ rsp - 0x28 ]
adcx r13, [ rsp - 0x30 ]
add r11, rbx
adc r13, 0x0
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], rdi
mulx rdi, rbx, rdx
mov rdx, r14
mov [ rsp + 0x130 ], r10
mulx r10, r14, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r14
adox r10, rcx
mov rcx, rbx
adcx rcx, [ rsp + 0xe8 ]
adcx rdi, [ rsp + 0xe0 ]
mov rbx, r15
add rbx, r11
adc r13, 0x0
mov rdx, [ rsi + 0x10 ]
mulx r14, r11, r9
mov rdx, 0x38 
bzhi r9, rbx, rdx
adox r8, rbp
adox r10, [ rsp + 0x130 ]
mov rbp, [ rsp + 0xa0 ]
mov rdx, rbp
add rdx, [ rsp + 0x68 ]
mov [ rsp + 0x138 ], r9
mov r9, [ rsp + 0x98 ]
adcx r9, [ rsp + 0x60 ]
xchg rdx, r12
mov [ rsp + 0x140 ], r9
mulx r9, rbp, [ rsi + 0x8 ]
add r8, [ rsp - 0x38 ]
adcx r10, [ rsp - 0x40 ]
test al, al
adox rcx, r11
adox r14, rdi
adcx rcx, rbp
adcx r9, r14
mov rdx, [ rsi + 0x8 ]
mulx r11, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, rbp, rdx
test al, al
adox r12, rdi
adox r11, [ rsp + 0x140 ]
shrd rbx, r13, 56
xor rdx, rdx
adox rcx, [ rsp + 0x20 ]
adox r9, [ rsp + 0x18 ]
mov r13, rbp
adcx r13, [ rsp + 0x118 ]
adcx r14, [ rsp + 0x110 ]
add r15, r13
adc r14, 0x0
xor rdi, rdi
adox r8, rbx
adox r10, rdi
mov rdx, r8
shrd rdx, r10, 56
mov rbp, r15
shrd rbp, r14, 56
mov rbx, [ rsp + 0x108 ]
xor r13, r13
adox rbx, [ rsp + 0xc0 ]
mov rdi, [ rsp + 0x100 ]
adox rdi, [ rsp + 0xb8 ]
mov r14, rdx
mov rdx, [ rsp - 0x48 ]
mulx r13, r10, [ rsi + 0x0 ]
adcx rbx, r10
adcx r13, rdi
xor rdx, rdx
adox rbx, rbp
adox r13, rdx
adcx rcx, r14
adc r9, 0x0
mov r14, 0xffffffffffffff 
mov rbp, rbx
and rbp, r14
mov rdi, rcx
and rdi, r14
shrd rcx, r9, 56
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x30 ], rdi
add r12, [ rsp + 0x50 ]
adcx r11, [ rsp + 0x48 ]
add rcx, [ rsp + 0x128 ]
and r15, r14
mov r9, rcx
shr r9, 56
and rcx, r14
and rax, r14
mov rdi, r9
add rdi, [ rsp + 0x138 ]
shrd rbx, r13, 56
add r12, rbx
adc r11, 0x0
mov r13, r12
shrd r13, r11, 56
lea r13, [ r13 + rax ]
mov rax, r13
and rax, r14
lea r15, [ r15 + r9 ]
mov [ r10 + 0x18 ], rax
mov r9, r15
and r9, r14
shr r13, 56
lea r13, [ r13 + rdi ]
mov rdi, r13
and rdi, r14
and r8, r14
mov [ r10 + 0x20 ], rdi
shr r13, 56
lea r13, [ r13 + r8 ]
mov [ r10 + 0x28 ], r13
shr r15, 56
lea r15, [ r15 + rbp ]
mov [ r10 + 0x38 ], rcx
and r12, r14
mov [ r10 + 0x10 ], r12
mov [ r10 + 0x0 ], r9
mov [ r10 + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 456
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0233
; seed 0824090629795883 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5440326 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=82, initial num_batches=31): 176151 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.032378758184711726
; number reverted permutation / tried permutation: 58779 / 89808 =65.450%
; number reverted decision / tried decision: 45366 / 90191 =50.300%
; validated in 2.049s
