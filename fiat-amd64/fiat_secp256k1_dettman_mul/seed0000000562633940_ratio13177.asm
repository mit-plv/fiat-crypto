SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x68 ], r13
mov r13, rcx
and r13, rdx
adox rbp, r9
adox rbx, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r9, [ rax + 0x18 ]
adcx rbp, r10
adcx r11, rbx
test al, al
adox rbp, r9
adox r12, r11
mov rdx, [ rax + 0x0 ]
mulx rbx, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mulx r11, r9, [ rsi + 0x18 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
adcx r10, r9
adcx r11, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, r13, [ rsi + 0x8 ]
xor rdx, rdx
adox r14, rbp
adox r12, r15
mov rbp, r14
shrd rbp, r12, 52
mov rdx, [ rax + 0x10 ]
mulx r15, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r12, [ rax + 0x20 ]
add r10, r9
adcx r15, r11
test al, al
adox r10, r13
adox rbx, r15
adcx r10, r12
adcx rdi, rbx
shrd rcx, r8, 52
xor rdx, rdx
adox rbp, r10
adox rdi, rdx
mov r8, 0x1000003d10 
mov rdx, r8
mulx r11, r8, rcx
adcx r8, rbp
adcx rdi, r11
mov r13, 0xfffffffffffff 
mov r9, r8
and r9, r13
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r10, rbx, [ rsi + 0x18 ]
shrd r8, rdi, 52
mov rdx, [ rsi + 0x20 ]
mulx rbp, rcx, [ rax + 0x8 ]
test al, al
adox rcx, rbx
adox r10, rbp
adcx rcx, r12
adcx r15, r10
mov rdx, [ rax + 0x20 ]
mulx rdi, r11, [ rsi + 0x8 ]
add rcx, r11
adcx rdi, r15
xor rdx, rdx
adox r8, rcx
adox rdi, rdx
mov r12, r8
and r12, r13
mov rdx, [ rax + 0x10 ]
mulx rbp, rbx, [ rsi + 0x20 ]
shl r12, 4
mov rdx, [ rax + 0x18 ]
mulx r15, r10, [ rsi + 0x18 ]
xor rdx, rdx
adox rbx, r10
adox r15, rbp
mov rdx, [ rax + 0x20 ]
mulx rcx, r11, [ rsi + 0x10 ]
adcx rbx, r11
adcx rcx, r15
shrd r8, rdi, 52
mov rdx, [ rsi + 0x0 ]
mulx rbp, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r15, r10, [ rsi + 0x20 ]
mov rdx, r9
shr rdx, 48
lea r12, [ r12 + rdx ]
xor r11, r11
adox r8, rbx
adox rcx, r11
mov rbx, 0x1000003d1 
mov rdx, r12
mulx r11, r12, rbx
mov rdx, r8
shrd rdx, rcx, 52
and r8, r13
adox r12, rdi
adox rbp, r11
mov rdi, r12
shrd rdi, rbp, 52
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mulx rbp, r11, [ rsi + 0x18 ]
xor rdx, rdx
adox r10, r11
adox rbp, r15
adcx rcx, r10
adc rbp, 0x0
mov r15, rcx
shrd r15, rbp, 52
mov rdx, [ rsi + 0x8 ]
mulx r10, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx rbx, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox rbp, r11
adox r10, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r15
mulx r15, r13, [ rsi + 0x0 ]
adcx r11, r13
adcx r15, rbx
xor rdx, rdx
adox rdi, r11
adox r15, rdx
mov rdx, [ rax + 0x10 ]
mulx r13, rbx, [ rsi + 0x0 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x40 ], r10
mulx r10, r11, r8
adcx r11, rdi
adcx r15, r10
mov r8, 0xfffffffffffff 
and rcx, r8
mulx r10, rdi, rcx
adox rbp, rbx
adox r13, [ rsp - 0x40 ]
mov rbx, r11
shrd rbx, r15, 52
xor r15, r15
adox rbx, rbp
adox r13, r15
adcx rdi, rbx
adcx r13, r10
mov rcx, rdi
and rcx, r8
shrd rdi, r13, 52
and r11, r8
mulx rbp, r10, [ rsp - 0x48 ]
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], rcx
and r14, r8
lea r14, [ r14 + rdi ]
adox r10, r14
adox rbp, r15
mov r13, 0xffffffffffff 
and r9, r13
mov rcx, r10
shrd rcx, rbp, 52
lea r9, [ r9 + rcx ]
mov [ rbx + 0x20 ], r9
mov [ rbx + 0x8 ], r11
and r10, r8
mov [ rbx + 0x18 ], r10
and r12, r8
mov [ rbx + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3177
; seed 4301882922392617 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 899749 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=277, initial num_batches=31): 81184 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09022960847969823
; number reverted permutation / tried permutation: 72963 / 89988 =81.081%
; number reverted decision / tried decision: 54126 / 90011 =60.133%
; validated in 0.278s
