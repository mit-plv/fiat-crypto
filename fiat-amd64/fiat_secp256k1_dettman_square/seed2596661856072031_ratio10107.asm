SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rsi + 0x0 ], rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x60 ], r14
mov r14, r11
and r14, rdx
mov rdx, r13
mov [ rsp - 0x58 ], r15
mulx r15, r13, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
adox rbp, r9
adox rbx, r12
mulx r12, r9, [ rsi + 0x18 ]
adcx rbp, rdi
adcx r10, rbx
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rdi
mulx rdi, rbx, r8
xor rdx, rdx
adox rbx, r9
adox r12, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r9, rdx
adcx r9, r13
adcx r15, rdi
mov rdx, 0x1000003d10 
mulx rdi, r13, r14
test al, al
adox r13, rbx
adox r12, rdi
mov r14, r13
shrd r14, r12, 52
add r14, rbp
adc r10, 0x0
mov rbp, [ rsi + 0x10 ]
mov rbx, rbp
shl rbx, 0x1
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbp, rbx
mov rdx, 0xfffffffffffff 
and r13, rdx
shrd r11, rcx, 52
mov rdx, rbx
mulx rcx, rbx, [ rsi + 0x20 ]
test al, al
adox rax, rbx
adox rcx, [ rsp - 0x48 ]
mov rdx, r8
mulx r12, r8, [ rsi + 0x20 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x30 ], r13
mulx r13, rbx, r11
adcx rbx, r14
adcx r10, r13
mov rdx, [ rsi + 0x0 ]
mulx r11, r14, rdx
mov rdx, 0xfffffffffffff 
mov r13, rbx
and r13, rdx
adox rbp, r8
adox r12, rdi
shrd rbx, r10, 52
add rbx, rbp
adc r12, 0x0
mov rdi, r13
shr rdi, 48
mov r8, rbx
and r8, rdx
shl r8, 4
lea r8, [ r8 + rdi ]
mov r10, 0x1000003d1 
mov rdx, r10
mulx rbp, r10, r8
xor rdi, rdi
adox r10, r14
adox r11, rbp
mov r14, 0xffffffffffff 
and r13, r14
imul r8, [ rsi + 0x18 ], 0x2
shrd rbx, r12, 52
mov rdx, [ rsi + 0x20 ]
mulx rbp, r12, r8
xor rdx, rdx
adox rbx, rax
adox rcx, rdx
mov rdi, rbx
shrd rdi, rcx, 52
test al, al
adox rdi, r12
adox rbp, rdx
mov rax, 0xfffffffffffff 
mov r8, rdi
and r8, rax
shrd rdi, rbp, 52
mov r12, 0x1000003d10 
mov rdx, r12
mulx rcx, r12, r8
mov rbp, r10
and rbp, rax
and rbx, rax
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], rbp
shrd r10, r11, 52
test al, al
adox r10, [ rsp - 0x38 ]
mov r11, [ rsp - 0x40 ]
mov rbp, 0x0 
adox r11, rbp
mulx r14, rbp, rbx
adcx rbp, r10
adcx r11, r14
mov rbx, rbp
shrd rbx, r11, 52
xor r10, r10
adox rbx, r9
adox r15, r10
adcx r12, rbx
adcx r15, rcx
mov r9, r12
shrd r9, r15, 52
mulx r14, rcx, rdi
add r9, [ rsp - 0x30 ]
and r12, rax
adox rcx, r9
adox r14, r10
mov [ r8 + 0x10 ], r12
mov rdi, rcx
shrd rdi, r14, 52
and rbp, rax
and rcx, rax
mov [ r8 + 0x18 ], rcx
lea r13, [ r13 + rdi ]
mov [ r8 + 0x8 ], rbp
mov [ r8 + 0x20 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0107
; seed 2596661856072031 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6291 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=243, initial num_batches=31): 466 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07407407407407407
; number reverted permutation / tried permutation: 410 / 513 =79.922%
; number reverted decision / tried decision: 337 / 486 =69.342%
; validated in 0.352s
