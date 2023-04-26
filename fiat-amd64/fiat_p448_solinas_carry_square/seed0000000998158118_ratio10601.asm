SECTION .text
	GLOBAL fiat_p448_solinas_carry_square
fiat_p448_solinas_carry_square:
sub rsp, 392
mov rax, 0x1 
shlx r10, [ rsi + 0x30 ], rax
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, rdx
shlx rdx, [ rsi + 0x28 ], rax
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rax, r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, r10
mov [ rsp - 0x70 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov r13, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
lea r14, [r13 + r13]
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, 0x1 
mov [ rsp - 0x48 ], rcx
shlx rcx, [ rsi + 0x8 ], rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], rdi
mulx rdi, r11, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x30 ], r15
lea r15, [rdx + rdx]
mov rdx, r15
mov [ rsp - 0x28 ], rcx
mulx rcx, r15, [ rsi + 0x20 ]
xchg rdx, r8
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r10
mulx r10, r12, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rax
mulx rax, r14, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], r12
mulx r12, r10, rdx
mov rdx, r10
mov [ rsp + 0x18 ], rax
xor rax, rax
adox rdx, r10
mov [ rsp + 0x20 ], r14
mov r14, r12
adox r14, r12
xchg rdx, r9
mov [ rsp + 0x28 ], rbp
mulx rbp, rax, [ rsi + 0x0 ]
adcx r9, r11
mov [ rsp + 0x30 ], rbp
mov rbp, rdi
adcx rbp, r14
mov [ rsp + 0x38 ], rax
mulx rax, r14, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], rax
mov [ rsp + 0x48 ], r14
mulx r14, rax, [ rsi + 0x8 ]
mov rdx, r13
mov [ rsp + 0x50 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], rax
xor rax, rax
adox r13, r15
adox rcx, r14
xchg rdx, r8
mulx r14, r15, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], rcx
mov rcx, rbx
adcx rcx, r15
mov [ rsp + 0x68 ], r13
mov r13, r14
adcx r13, [ rsp + 0x28 ]
mov rax, 0x1 
mov [ rsp + 0x70 ], rbp
shlx rbp, [ rsi + 0x20 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rbp
mulx rbp, r9, rdx
mov rdx, rcx
add rdx, rbx
mov [ rsp + 0x88 ], rbp
mov rbp, r13
adcx rbp, [ rsp + 0x28 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], rbp
mov [ rsp + 0x98 ], r9
mulx r9, rbp, [ rsp + 0x80 ]
xor rdx, rdx
adox r10, r11
adox rdi, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, r11, rax
adcx rcx, [ rsp + 0x98 ]
adcx r13, [ rsp + 0x88 ]
mov rdx, r8
mov [ rsp + 0xa0 ], r12
mulx r12, r8, [ rsi + 0x20 ]
test al, al
adox rcx, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
mov [ rsp + 0xa8 ], r11
mov r11, r8
adcx r11, [ rsp + 0x78 ]
mov [ rsp + 0xb0 ], r13
mov r13, r12
adcx r13, [ rsp + 0x70 ]
mov [ rsp + 0xb8 ], r13
xor r13, r13
adox r10, r8
adox r12, rdi
mulx r8, rdi, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r11
mov r11, rbp
adcx r11, [ rsp + 0x68 ]
adcx r9, [ rsp + 0x60 ]
add r11, [ rsp + 0x10 ]
adcx r9, [ rsp + 0x8 ]
test al, al
adox r11, rdi
adox r8, r9
xchg rdx, rax
mulx rdi, rbp, [ rsi + 0x0 ]
adcx r11, rbp
adcx rdi, r8
xor r9, r9
adox rbx, r15
adox r14, [ rsp + 0x90 ]
mov r13, 0xffffffffffffff 
mov r15, r11
and r15, r13
shrd r11, rdi, 56
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, rdx
add rbx, [ rsp + 0x98 ]
adcx r14, [ rsp + 0x88 ]
add rbx, [ rsp + 0x20 ]
adcx r14, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, r9, rax
xor rdx, rdx
adox rcx, r9
mov [ rsp + 0xc8 ], r15
mov r15, r13
adox r15, [ rsp + 0xb0 ]
adcx rbx, r9
adcx r13, r14
test al, al
adox rbx, rbp
adox rdi, r13
mov rdx, r8
mulx rbp, r8, [ rsi + 0x8 ]
adcx rbx, r8
mov r14, rbp
adcx r14, rdi
add rcx, r8
adcx rbp, r15
imul r9, [ rsi + 0x18 ], 0x2
test al, al
adox rcx, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], r12
mulx r12, r8, r9
mov rdx, r11
adcx rdx, rcx
adc rbp, 0x0
mov rcx, rdx
shrd rcx, rbp, 56
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r12
mov [ rsp + 0xe0 ], r8
mulx r8, r12, r9
test al, al
adox rbx, r12
adox r8, r14
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, r9
mov rdx, r13
adcx rdx, [ rsp + 0x68 ]
adcx rdi, [ rsp + 0x60 ]
test al, al
adox rdx, r14
adox r12, rdi
mov r9, 0x38 
bzhi r13, rbp, r9
mov rbp, rdx
shrd rbp, r12, 56
xchg rdx, r15
mulx rdi, r14, [ rsi + 0x30 ]
mov r12, r14
xor r9, r9
adox r12, [ rsp + 0x48 ]
mov [ rsp + 0xe8 ], r13
mov r13, rdi
adox r13, [ rsp + 0x40 ]
mov r9, 0xffffffffffffff 
and r15, r9
adox r12, [ rsp - 0x18 ]
adox r13, [ rsp - 0x20 ]
mov r9, rdx
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0xf0 ], r15
mov [ rsp + 0xf8 ], r10
mulx r10, r15, [ rsi + 0x0 ]
adcx rbx, r15
adcx r10, r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x100 ], rcx
mulx rcx, r15, r9
xor rdx, rdx
adox rbx, rbp
adox r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rsp - 0x28 ]
adcx r12, r15
mov rdx, rcx
adcx rdx, r13
mov r13, r14
add r13, r14
adcx rdi, rdi
add r12, r9
adcx rbp, rdx
add r12, [ rsp + 0x100 ]
adc rbp, 0x0
add r11, rbx
adc r10, 0x0
add r13, [ rsp + 0x48 ]
adcx rdi, [ rsp + 0x40 ]
add r13, [ rsp - 0x18 ]
adcx rdi, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r14, r8
xor rdx, rdx
adox r13, r15
adox rcx, rdi
mov r15, [ rsp + 0xf8 ]
adcx r15, [ rsp + 0xa8 ]
mov r9, [ rsp + 0xd0 ]
adcx r9, [ rsp + 0xa0 ]
xor rdi, rdi
adox r13, [ rsp + 0xe0 ]
adox rcx, [ rsp + 0xd8 ]
adcx r13, r14
adcx rbx, rcx
test al, al
adox r15, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx r13, [ rsp + 0x38 ]
adcx rbx, [ rsp + 0x30 ]
mov rdx, r11
shrd rdx, r10, 56
mov r10, rdx
mov rdx, [ rsp - 0x10 ]
mulx rcx, r14, [ rsi + 0x0 ]
mov rdx, r12
shrd rdx, rbp, 56
test al, al
adox r13, r10
adox rbx, rdi
adcx r15, r14
adcx rcx, r9
test al, al
adox r15, rdx
adox rcx, rdi
mov rbp, r13
shrd rbp, rbx, 56
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, r8
mov rdx, r15
shrd rdx, rcx, 56
mov r8, [ rsp + 0xa8 ]
mov r14, r8
test al, al
adox r14, [ rsp + 0xc0 ]
mov rbx, [ rsp + 0xa0 ]
adox rbx, [ rsp + 0xb8 ]
mov r8, 0xffffffffffffff 
and r15, r8
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], r15
adox r14, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
add rdx, [ rsp + 0xf0 ]
test al, al
adox r14, r9
adox r10, rbx
adcx r14, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x50 ]
mov r9, rdx
and r9, r8
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbx, rax
adox r14, rbx
adox rdi, r10
mov [ rcx + 0x18 ], r9
adcx r14, rbp
adc rdi, 0x0
mov rdx, r14
and rdx, r8
shrd r14, rdi, 56
add r14, [ rsp + 0xc8 ]
mov [ rcx + 0x30 ], rdx
and r11, r8
mov rax, r14
shr rax, 56
mov rbp, rax
add rbp, [ rsp + 0xe8 ]
and r14, r8
mov r10, rbp
shr r10, 56
lea r11, [ r11 + rax ]
shr r15, 56
and rbp, r8
lea r15, [ r15 + r11 ]
and r13, r8
mov r9, r15
and r9, r8
shr r15, 56
lea r15, [ r15 + r13 ]
and r12, r8
lea r10, [ r10 + r12 ]
mov [ rcx + 0x0 ], rbp
mov [ rcx + 0x8 ], r10
mov [ rcx + 0x20 ], r9
mov [ rcx + 0x38 ], r14
mov [ rcx + 0x28 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 392
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0601
; seed 1843136722129740 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3250258 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=137, initial num_batches=31): 117630 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03619097314736246
; number reverted permutation / tried permutation: 63741 / 89991 =70.830%
; number reverted decision / tried decision: 50444 / 90008 =56.044%
; validated in 1.445s
