SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
adcx r8, r10
adox r8, r8
adcx r12, r9
adcx r11, r13
adcx rbx, rcx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rsi + 0x10 ]
setc dl
clc
adcx r10, r12
movzx r9, dl
lea r9, [ r9 + rbp ]
adox r10, r10
adcx rcx, r11
mov rbp, 0x0 
mov r13, rbp
adcx r13, rbx
adox rcx, rcx
adox r13, r13
mov r12, rbp
adcx r12, r9
mov rdx, [ rsi + 0x0 ]
mulx rbx, r11, rdx
setc dl
clc
adcx rbx, rax
adox r12, r12
movzx rax, dl
adox rax, rbp
adcx r14, r8
movzx r8, dl
lea r8, [ r8 + rax ]
adcx r15, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, rdx
adcx r9, rcx
adcx r10, r13
mov rdx, 0x26 
mulx r13, rcx, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, rdx
adcx rax, r12
adcx r8, r10
mov rdx, 0x26 
mulx r10, r12, rax
xor rax, rax
adox rcx, rbx
mulx rbx, rbp, r9
adox r12, r14
mulx r9, r14, r8
adcx rbp, r11
adcx rbx, rcx
adox r14, r15
adox r9, rax
adcx r13, r12
adcx r10, r14
adc r9, 0x0
mulx r15, r11, r9
xor r15, r15
adox r11, rbp
mov rax, r15
adox rax, rbx
mov r8, r15
adox r8, r13
mov rcx, r15
adox rcx, r10
mov [ rdi + 0x8 ], rax
mov r12, r15
cmovo r12, rdx
mov [ rdi + 0x18 ], rcx
adcx r11, r12
mov [ rdi + 0x0 ], r11
mov [ rdi + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.3479
; seed 0176560831898932 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 824916 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=517, initial num_batches=31): 127377 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.15441208559416958
; number reverted permutation / tried permutation: 64352 / 90201 =71.343%
; number reverted decision / tried decision: 47963 / 89798 =53.412%
; validated in 0.549s
