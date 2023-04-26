SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
imul r10, [ rsi + 0x18 ], 0x26
imul r11, [ rsi + 0x18 ], 0x13
mov rdx, [ rsi + 0x20 ]
lea rcx, [rdx + 8 * rdx]
lea r8, [rdx + 2 * rcx]
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, r10
mov rdx, 0x1 
shlx r10, [ rsi + 0x10 ], rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
lea r14, [rdx + rdx]
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, r8
mov [ rsp - 0x50 ], rdi
mulx rdi, r8, [ rsi + 0x20 ]
add r8, rbx
adcx rbp, rdi
mov rdx, rax
mulx rbx, rax, [ rsi + 0x8 ]
xor rdi, rdi
adox rcx, rax
adox rbx, r9
mulx rax, r9, [ rsi + 0x10 ]
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], r8
mulx r8, rbp, r11
adcx rbp, r9
adcx rax, r8
add rcx, r12
adcx r13, rbx
mov rdx, r10
mulx r11, r10, [ rsi + 0x0 ]
add rbp, r14
adcx r15, rax
mov rdx, rcx
shrd rdx, r13, 51
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r14, rdx
mov rdx, rdi
mulx r9, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
lea r8, [rdx + rdx]
mov rdx, r8
mulx rax, r8, [ rsi + 0x0 ]
mov r13, r8
add r13, [ rsp - 0x40 ]
adcx rax, [ rsp - 0x48 ]
xor r8, r8
adox rdi, r14
adox rbx, r9
adcx rdi, r10
adcx r11, rbx
xor r10, r10
adox rbp, r12
adox r15, r10
mov r8, rbp
shrd r8, r15, 51
mov r12, 0x33 
bzhi r14, rbp, r12
adox rdi, r8
adox r11, r10
mov r9, rdi
shrd r9, r11, 51
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, r15, rdx
mov rdx, [ rsi + 0x20 ]
lea r11, [rdx + rdx]
xor rdx, rdx
adox r15, rbx
adox rbp, r8
bzhi r10, rcx, r12
mov rdx, [ rsi + 0x0 ]
mulx rbx, rcx, r11
adox r15, rcx
adox rbx, rbp
add r13, r9
adc rax, 0x0
bzhi rdx, r13, r12
bzhi r9, rdi, r12
shrd r13, rax, 51
xor rdi, rdi
adox r15, r13
adox rbx, rdi
mov r8, r15
shrd r8, rbx, 51
bzhi r11, r15, r12
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x20 ], r11
imul rcx, r8, 0x13
lea r10, [ r10 + rcx ]
mov rax, r10
shr rax, 51
lea rax, [ rax + r14 ]
bzhi r14, rax, r12
shr rax, 51
lea rax, [ rax + r9 ]
bzhi r9, r10, r12
mov [ rbp + 0x8 ], r14
mov [ rbp + 0x18 ], rdx
mov [ rbp + 0x0 ], r9
mov [ rbp + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2147
; seed 2768923078540193 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7430 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=235, initial num_batches=31): 676 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09098250336473755
; number reverted permutation / tried permutation: 405 / 486 =83.333%
; number reverted decision / tried decision: 383 / 513 =74.659%
; validated in 0.366s
