SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
xor r11, r11
adox rax, rax
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x18 ]
adcx r12, r10
adcx r14, r13
adcx rdi, r15
adcx r9, rbx
mov rdx, 0x0 
adcx r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r10, [ rsi + 0x10 ]
clc
adcx r10, r14
adox r12, r12
adcx r13, rdi
mov rdx, 0x0 
mov r15, rdx
adcx r15, r9
adox r10, r10
mov rbx, rdx
adcx rbx, r11
setc r14b
clc
adcx rbp, rax
adox r13, r13
mov rdx, [ rsi + 0x8 ]
mulx rdi, rax, rdx
adcx rax, r12
adcx rdi, r10
adox r15, r15
mov rdx, [ rsi + 0x10 ]
mulx r11, r9, rdx
adcx r9, r13
adox rbx, rbx
adcx r11, r15
mov rdx, 0x26 
mulx r10, r12, r11
movzx r13, r14b
mov r15, 0x0 
adox r13, r15
adcx rcx, rbx
movzx rbx, r14b
lea rbx, [ rbx + r13 ]
adcx rbx, r8
mulx r14, r8, rbx
xor r11, r11
adox r12, rbp
mulx rbp, r15, r9
adcx r15, [ rsp - 0x48 ]
mulx r13, r9, rcx
adcx rbp, r12
adox r9, rax
adox r8, rdi
adox r14, r11
adcx r10, r9
adcx r13, r8
adc r14, 0x0
mulx rdi, rax, r14
xor rdi, rdi
adox rax, r15
mov r11, rdi
adox r11, rbp
mov rcx, rdi
adox rcx, r10
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], r11
mov [ rbx + 0x10 ], rcx
mov r12, rdi
adox r12, r13
mov r15, rdi
cmovo r15, rdx
adcx rax, r15
mov [ rbx + 0x18 ], r12
mov [ rbx + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4851
; seed 0599576456341778 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3122 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=320, initial num_batches=31): 320 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.10249839846252402
; number reverted permutation / tried permutation: 380 / 495 =76.768%
; number reverted decision / tried decision: 297 / 504 =58.929%
; validated in 0.379s
