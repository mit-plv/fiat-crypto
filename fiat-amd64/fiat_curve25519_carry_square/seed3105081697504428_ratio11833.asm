SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x10 ], rax
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, r10
imul rdx, [ rsi + 0x20 ], 0x26
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
xor r13, r13
adox rax, r11
adox rcx, rbx
mov r11, [ rsi + 0x20 ]
lea rbx, [r11 + r11]
imul r11, [ rsi + 0x20 ], 0x13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, [ rsi + 0x8 ]
mov r11, rdx
shl r11, 0x1
add r14, r8
adcx r9, r15
mov rdx, [ rsi + 0x0 ]
mulx r15, r8, r10
mov rdx, [ rsi + 0x18 ]
lea r10, [rdx + rdx]
mov rdx, r10
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rbx
imul rbx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r9
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, rbp
adox r12, r9
adcx rax, r8
adcx r15, rcx
imul rbp, [ rsi + 0x18 ], 0x13
xor rcx, rcx
adox r14, r10
adox rdi, [ rsp - 0x38 ]
mov rdx, r13
mulx r8, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r10, rdx
mov rdx, rbp
mulx rcx, rbp, [ rsi + 0x18 ]
adcx rbx, r10
adcx r9, r12
add rbp, r13
adcx r8, rcx
mov rdx, [ rsp - 0x40 ]
mulx r13, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r12
adox r13, r8
mov r10, rbx
shrd r10, r9, 51
xor rcx, rcx
adox rbp, r10
adox r13, rcx
mov rdx, rbp
shrd rdx, r13, 51
mov r9, 0x7ffffffffffff 
and rbx, r9
adox rax, rdx
adox r15, rcx
and rbp, r9
mov r8, rax
shrd r8, r15, 51
add r14, r8
adc rdi, 0x0
mov r12, r14
shrd r12, rdi, 51
and r14, r9
mov rdx, [ rsi + 0x10 ]
mulx r13, r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rsp - 0x48 ]
and rax, r9
adox r10, r11
adox r13, [ rsp - 0x30 ]
adcx r10, r15
adcx r8, r13
xor rdx, rdx
adox r10, r12
adox r8, rdx
mov rcx, r10
and rcx, r9
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x20 ], rcx
shrd r10, r8, 51
imul rdi, r10, 0x13
lea rbx, [ rbx + rdi ]
mov r12, rbx
and r12, r9
shr rbx, 51
lea rbx, [ rbx + rbp ]
mov [ r11 + 0x0 ], r12
mov rbp, rbx
and rbp, r9
mov [ r11 + 0x8 ], rbp
shr rbx, 51
lea rbx, [ rbx + rax ]
mov [ r11 + 0x18 ], r14
mov [ r11 + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1833
; seed 3105081697504428 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4966 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=255, initial num_batches=31): 467 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09403946838501813
; number reverted permutation / tried permutation: 408 / 507 =80.473%
; number reverted decision / tried decision: 361 / 492 =73.374%
; validated in 0.332s
