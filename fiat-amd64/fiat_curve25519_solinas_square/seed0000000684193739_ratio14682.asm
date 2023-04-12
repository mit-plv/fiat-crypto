SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, rcx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
adox r8, r10
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
adcx rbx, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
adox r8, r9
adox r13, r12
mov rdx, 0x0 
adox r14, rdx
adcx rbp, r8
mov r9, rdx
adcx r9, r13
mov r12, -0x3 
inc r12
adox r11, r11
adox rax, rax
mov r8, rdx
adcx r8, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, r13, rdx
setc dl
clc
adcx r14, r11
adox rbx, rbx
adox rbp, rbp
adox r9, r9
adox r8, r8
mov r11b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r12, r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, rdx
adcx r15, rax
adcx r12, rbx
adcx rdi, rbp
adcx r13, r9
adcx r10, r8
movzx rdx, r11b
mov rax, 0x0 
adox rdx, rax
movzx rbx, r11b
lea rbx, [ rbx + rdx ]
adcx rbx, rcx
mov rcx, 0x26 
mov rdx, rcx
mulx r11, rcx, rbx
mulx r9, rbp, r13
mulx r13, r8, rdi
test al, al
adox rbp, r14
mulx rdi, r14, r10
adox r14, r15
adcx r8, [ rsp - 0x48 ]
adcx r13, rbp
adcx r9, r14
adox rcx, r12
adox r11, rax
adcx rdi, rcx
adc r11, 0x0
mulx r12, r15, r11
test al, al
adox r15, r8
mov r12, rax
adox r12, r13
mov r10, rax
adox r10, r9
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], r12
mov [ rbx + 0x10 ], r10
mov rbp, rax
adox rbp, rdi
mov r14, rax
cmovo r14, rdx
adcx r15, r14
mov [ rbx + 0x0 ], r15
mov [ rbx + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4682
; seed 3170922214205802 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 518677 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=321, initial num_batches=31): 61918 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11937679904834801
; number reverted permutation / tried permutation: 73194 / 90358 =81.004%
; number reverted decision / tried decision: 51630 / 89641 =57.596%
; validated in 0.376s
