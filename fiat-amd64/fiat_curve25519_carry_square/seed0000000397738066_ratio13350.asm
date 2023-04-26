SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x8 ]
lea r10, [rax + rax]
imul rax, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rax
imul rdx, [ rsi + 0x20 ], 0x26
mulx r9, r8, [ rsi + 0x8 ]
xor rax, rax
adox r11, r8
adox r9, rcx
mulx r8, rcx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
imul rdx, [ rsi + 0x18 ], 0x13
mov [ rsp - 0x68 ], r13
xor r13, r13
adox r11, rbp
adox r12, r9
mulx rbp, r9, [ rsi + 0x18 ]
adcx r9, rcx
adcx r8, rbp
mov rdx, r10
mulx rcx, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r10
adox rcx, r8
mov rdx, [ rsi + 0x8 ]
mulx rbp, r13, rdx
mov rdx, r11
shrd rdx, r12, 51
xor r12, r12
adox r9, rdx
adox rcx, r12
mov r8, r9
shrd r8, rcx, 51
mov r10, [ rsi + 0x10 ]
mov rdx, r10
shl rdx, 0x1
add rax, r13
adcx rbp, rbx
mulx rbx, r10, [ rsi + 0x0 ]
test al, al
adox rax, r10
adox rbx, rbp
adcx rax, r8
adc rbx, 0x0
mov r13, rax
shrd r13, rbx, 51
mov rcx, [ rsi + 0x20 ]
lea r8, [rcx + 8 * rcx]
lea rbp, [rcx + 2 * r8]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, rbp
mulx r10, rbp, [ rsi + 0x20 ]
xor rbx, rbx
adox rbp, rcx
adox r8, r10
mov r12, [ rsi + 0x18 ]
lea rdx, [r12 + r12]
mulx rcx, r12, [ rsi + 0x0 ]
mov r10, 0x7ffffffffffff 
and rax, r10
adox rbp, r12
adox rcx, r8
adcx rbp, r13
adc rcx, 0x0
mov r13, rbp
and r13, r10
shrd rbp, rcx, 51
mov r8, [ rsi + 0x20 ]
lea r12, [r8 + r8]
mulx rcx, r8, [ rsi + 0x8 ]
mov [ rdi + 0x18 ], r13
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, rdx
add r13, r8
adcx rcx, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r8, r12
xor rdx, rdx
adox r13, r8
adox rbx, rcx
adcx r13, rbp
adc rbx, 0x0
mov rbp, r13
shrd rbp, rbx, 51
imul r12, rbp, 0x13
and r13, r10
and r9, r10
and r11, r10
mov [ rdi + 0x20 ], r13
lea r11, [ r11 + r12 ]
mov rcx, r11
and rcx, r10
shr r11, 51
lea r11, [ r11 + r9 ]
mov r8, r11
and r8, r10
shr r11, 51
lea r11, [ r11 + rax ]
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x0 ], rcx
mov [ rdi + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3350
; seed 1937382936230726 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 480039 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=538, initial num_batches=31): 72119 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.15023571001522792
; number reverted permutation / tried permutation: 70246 / 89920 =78.121%
; number reverted decision / tried decision: 68331 / 90079 =75.857%
; validated in 0.169s
