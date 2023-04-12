SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x0 ], 0x2
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x78 ], rbp
mov rbp, rcx
and rbp, rdx
mov [ rsp - 0x70 ], r12
mov r12, 0x1000003d10 
mov rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbp, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
shl r15, 0x1
mov rdx, r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], rax
mulx rax, r10, [ rsi + 0x20 ]
add r9, r15
adcx rdi, rbx
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, r11
mov [ rsp - 0x38 ], r14
mulx r14, r11, [ rsi + 0x18 ]
add rbx, r11
adcx r14, r15
mulx r11, r15, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rbp
xor rbp, rbp
adox r9, r15
adox r11, rdi
mulx r15, rdi, [ rsi + 0x10 ]
adcx r12, rbx
adcx r14, r13
shrd rcx, r8, 52
mov rdx, 0x34 
bzhi r8, r12, rdx
shrd r12, r14, 52
mov r13, 0x1000003d10 
mov rdx, rcx
mulx rbx, rcx, r13
test al, al
adox r12, r9
adox r11, rbp
adcx rcx, r12
adcx r11, rbx
mov r9, 0xfffffffffffff 
mov r14, rcx
and r14, r9
mov rdx, [ rsi + 0x10 ]
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mulx rbp, r12, rbx
adox r12, r10
adox rax, rbp
shrd rcx, r11, 52
xor rdx, rdx
adox rcx, r12
adox rax, rdx
mov r10, rcx
and r10, r9
shl r10, 4
mov r11, r14
shr r11, 48
lea r10, [ r10 + r11 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, rdx
mov rdx, 0x1000003d1 
mulx r13, r11, r10
add r11, rbp
adcx r12, r13
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, rdx
mov rdx, 0xffffffffffff 
and r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, rbx
adox r10, r13
adox r9, rbp
shrd rcx, rax, 52
xor rdx, rdx
adox rcx, r10
adox r9, rdx
mov rbx, 0x34 
bzhi rax, rcx, rbx
imul rbp, [ rsi + 0x18 ], 0x2
mov r13, 0x1000003d10 
mov rdx, r13
mulx r10, r13, rax
shrd rcx, r9, 52
mov rdx, rbp
mulx r9, rbp, [ rsi + 0x20 ]
xor rax, rax
adox rcx, rbp
adox r9, rax
bzhi rdx, rcx, rbx
shrd rcx, r9, 52
mov rbp, r11
shrd rbp, r12, 52
add rbp, [ rsp - 0x30 ]
mov r12, [ rsp - 0x38 ]
adc r12, 0x0
test al, al
adox r13, rbp
adox r12, r10
mov r10, 0x1000003d10 
mulx rbp, r9, r10
mov rdx, rdi
adcx rdx, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
bzhi rdi, r13, rbx
shrd r13, r12, 52
test al, al
adox r13, rdx
adox r15, rax
adcx r9, r13
adcx r15, rbp
bzhi r12, r9, rbx
shrd r9, r15, 52
lea r8, [ r8 + r9 ]
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], r12
mov rdx, r10
mulx r13, r10, rcx
bzhi rcx, r11, rbx
adox r10, r8
adox r13, rax
bzhi r11, r10, rbx
mov [ rbp + 0x18 ], r11
shrd r10, r13, 52
lea r14, [ r14 + r10 ]
mov [ rbp + 0x8 ], rdi
mov [ rbp + 0x0 ], rcx
mov [ rbp + 0x20 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0448
; seed 2742055397354950 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1058552 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=245, initial num_batches=31): 84811 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08011982406154823
; number reverted permutation / tried permutation: 75647 / 90030 =84.024%
; number reverted decision / tried decision: 64458 / 89969 =71.645%
; validated in 0.343s
