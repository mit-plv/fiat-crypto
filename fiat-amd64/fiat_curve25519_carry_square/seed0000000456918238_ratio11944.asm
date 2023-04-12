SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x13
mov r10, [ rsi + 0x8 ]
mov r11, r10
shl r11, 0x1
imul r10, [ rsi + 0x20 ], 0x26
imul rdx, [ rsi + 0x18 ], 0x26
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, rax
mulx r9, rax, [ rsi + 0x18 ]
mov rdx, r10
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
add rax, r10
adcx rbx, r9
mulx r10, r9, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
add rcx, r9
adcx r10, r8
mov rdx, r11
mulx r8, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, r12
adox r13, r10
mov r9, rcx
shrd r9, r13, 51
add rax, r11
adcx r8, rbx
mov rbx, [ rsi + 0x10 ]
lea r12, [rbx + rbx]
test al, al
adox rax, r9
adox r8, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, rdx
mov rdx, rbp
mulx r11, rbp, [ rsi + 0x18 ]
adcx rbp, rbx
adcx r10, r11
mov rdx, [ rsi + 0x0 ]
mulx r9, r13, r12
add rbp, r13
adcx r9, r10
mov rdx, rax
shrd rdx, r8, 51
imul r8, [ rsi + 0x20 ], 0x13
xor rbx, rbx
adox rbp, rdx
adox r9, rbx
mov rdx, r8
mulx r11, r8, [ rsi + 0x20 ]
mov rdx, r12
mulx r10, r12, [ rsi + 0x8 ]
adcx r8, r12
adcx r10, r11
mov rdx, [ rsi + 0x18 ]
mov r13, rdx
shl r13, 0x1
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, rdx
mov rdx, r13
mulx rbx, r13, [ rsi + 0x8 ]
test al, al
adox r11, r13
adox rbx, r12
mulx r13, r12, [ rsi + 0x0 ]
adcx r8, r12
adcx r13, r10
mov r10, [ rsi + 0x20 ]
mov rdx, r10
shl rdx, 0x1
mulx r12, r10, [ rsi + 0x0 ]
mov rdx, rbp
shrd rdx, r9, 51
xor r9, r9
adox r8, rdx
adox r13, r9
mov rdx, r8
shrd rdx, r13, 51
xor r13, r13
adox r11, r10
adox r12, rbx
mov r9, 0x7ffffffffffff 
and r8, r9
adox r11, rdx
adox r12, r13
mov rbx, r11
and rbx, r9
shrd r11, r12, 51
and rcx, r9
imul r10, r11, 0x13
and rax, r9
lea rcx, [ rcx + r10 ]
mov rdx, rcx
shr rdx, 51
lea rdx, [ rdx + rax ]
mov r12, rdx
and r12, r9
and rbp, r9
mov [ rdi + 0x8 ], r12
and rcx, r9
shr rdx, 51
lea rdx, [ rdx + rbp ]
mov [ rdi + 0x0 ], rcx
mov [ rdi + 0x10 ], rdx
mov [ rdi + 0x20 ], rbx
mov [ rdi + 0x18 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1944
; seed 2291132485193624 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 521262 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=486, initial num_batches=31): 73501 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.14100586653160982
; number reverted permutation / tried permutation: 72043 / 90290 =79.791%
; number reverted decision / tried decision: 69347 / 89709 =77.302%
; validated in 0.194s
