SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rdx
imul rdx, [ rsi + 0x0 ], 0x2
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x50 ], rdi
mov rdi, rax
and rdi, rdx
mov rdx, 0x1000003d10 
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, rdi
adox r12, r9
adox rbx, r13
shrd rax, r10, 52
mov rdx, [ rsi + 0x10 ]
mulx r9, r10, rdx
test al, al
adox r10, r14
adox r15, r9
mov rdx, rbp
mulx r13, rbp, [ rsi + 0x20 ]
mov r14, 0x1000003d10 
xchg rdx, rax
mulx r9, rdi, r14
adcx r8, r12
adcx rbx, rcx
mov rcx, r8
shrd rcx, rbx, 52
add r10, rbp
adcx r13, r15
xor r12, r12
adox rcx, r10
adox r13, r12
adcx rdi, rcx
adcx r13, r9
mov rdx, 0x34 
bzhi r15, rdi, rdx
mov rbp, r15
shr rbp, 48
mov rdx, [ rsi + 0x18 ]
mulx rbx, r9, rdx
mov rdx, 0x1 
shlx r10, [ rsi + 0x10 ], rdx
shrd rdi, r13, 52
mov rdx, [ rsi + 0x20 ]
mulx r13, rcx, r10
mov rdx, r10
mulx r12, r10, [ rsi + 0x18 ]
add r9, rcx
adcx r13, rbx
mov rdx, r11
mulx rbx, r11, [ rsi + 0x20 ]
add r10, r11
adcx rbx, r12
xor rdx, rdx
adox rdi, r10
adox rbx, rdx
mov rcx, 0x34 
bzhi r12, rdi, rcx
shrd rdi, rbx, 52
test al, al
adox rdi, r9
adox r13, rdx
shl r12, 4
lea r12, [ r12 + rbp ]
mov rbp, 0x1000003d1 
mov rdx, r12
mulx r9, r12, rbp
xor r11, r11
adox r12, [ rsp - 0x40 ]
adox r9, [ rsp - 0x48 ]
mov r10, r12
shrd r10, r9, 52
mov rbx, [ rsi + 0x18 ]
mov rdx, rbx
shl rdx, 0x1
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, rdi
shrd rdx, r13, 52
xor r13, r13
adox rdx, rbx
adox r9, r13
bzhi r11, r12, rcx
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, rbx, rax
adox r10, rbx
mov rdx, 0x0 
adox r13, rdx
bzhi rbx, rdi, rcx
mov rdx, r14
mulx rdi, r14, rbx
adox r14, r10
adox r13, rdi
mov r10, r12
shrd r10, r9, 52
bzhi r9, r8, rcx
bzhi r8, r14, rcx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], r8
mov rdx, [ rsi + 0x8 ]
mulx r8, rdi, rdx
shrd r14, r13, 52
mov rdx, rax
mulx r13, rax, [ rsi + 0x10 ]
bzhi rdx, r12, rcx
mov r12, 0x1000003d10 
mulx rbp, rcx, r12
adox rdi, rax
adox r13, r8
xor r8, r8
adox r14, rdi
adox r13, r8
adcx rcx, r14
adcx r13, rbp
mov rax, 0xfffffffffffff 
mov rdx, rcx
and rdx, rax
shrd rcx, r13, 52
mov [ rbx + 0x10 ], rdx
mov rdx, r12
mulx rbp, r12, r10
lea r9, [ r9 + rcx ]
mov r10, 0x30 
bzhi rdi, r15, r10
adox r12, r9
adox rbp, r8
mov r15, r12
shrd r15, rbp, 52
lea rdi, [ rdi + r15 ]
and r12, rax
mov [ rbx + 0x20 ], rdi
mov [ rbx + 0x0 ], r11
mov [ rbx + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0222
; seed 2373067137062781 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1654251 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=225, initial num_batches=31): 131897 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07973215672833203
; number reverted permutation / tried permutation: 73123 / 90035 =81.216%
; number reverted decision / tried decision: 63180 / 89964 =70.228%
; validated in 0.37s
