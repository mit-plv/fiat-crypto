SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, 0xfffffffffffff 
mov rdx, rax
and rdx, r11
mov rcx, 0x1000003d10 
mulx r9, r8, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
adox rbp, r14
adox r15, r12
adcx r8, rbp
adcx r15, r9
mov rdx, r8
shrd rdx, r15, 52
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, rdx
mov rdx, rbx
mulx rbp, rbx, [ rsi + 0x18 ]
xor r15, r15
adox r12, rbx
adox rbp, r14
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, rbx, r13
adcx r12, rbx
adcx r15, rbp
xor rdx, rdx
adox r9, r12
adox r15, rdx
shrd rax, r10, 52
mov rdx, rcx
mulx r10, rcx, rax
xor rbp, rbp
adox rcx, r9
adox r15, r10
mov rbx, rcx
and rbx, r11
mov r12, [ rsi + 0x10 ]
lea r9, [r12 + r12]
mov rdx, r14
mulx r14, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, r9
shrd rcx, r15, 52
xor rdx, rdx
adox rax, r12
adox r14, r10
adcx rcx, rax
adc r14, 0x0
mov rbp, rcx
shrd rbp, r14, 52
and rcx, r11
mov r15, rbx
shr r15, 48
mov rdx, [ rsi + 0x18 ]
mulx r10, r12, rdx
shl rcx, 4
lea rcx, [ rcx + r15 ]
mov rdx, r9
mulx rax, r9, [ rsi + 0x20 ]
xor rdx, rdx
adox r12, r9
adox rax, r10
adcx rbp, r12
adc rax, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, r13
mov rdx, 0x1000003d1 
mulx r9, r10, rcx
mov rdx, [ rsi + 0x0 ]
mulx r12, rcx, rdx
xor rdx, rdx
adox r10, rcx
adox r12, r9
mov r9, rbp
and r9, r11
mov rcx, 0x1000003d10 
mov rdx, r9
mulx r11, r9, rcx
mov rdx, r10
shrd rdx, r12, 52
add rdx, r14
adc r15, 0x0
add r9, rdx
adcx r15, r11
mov r14, r9
shrd r14, r15, 52
mov r12, [ rsi + 0x18 ]
lea r11, [r12 + r12]
mov r12, 0xfffffffffffff 
and r10, r12
and r9, r12
mov [ rdi + 0x0 ], r10
mov rdx, r11
mulx r15, r11, [ rsi + 0x20 ]
mov [ rdi + 0x8 ], r9
shrd rbp, rax, 52
add rbp, r11
adc r15, 0x0
mov rdx, r13
mulx rax, r13, [ rsi + 0x10 ]
mov rdx, rbp
shrd rdx, r15, 52
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r9, rdx
and r8, r12
adox r9, r13
adox rax, r11
adcx r14, r9
adc rax, 0x0
and rbp, r12
mov rdx, rcx
mulx r15, rcx, rbp
adox rcx, r14
adox rax, r15
mov r13, rcx
and r13, r12
mov [ rdi + 0x10 ], r13
mulx r9, r11, r10
shrd rcx, rax, 52
lea r8, [ r8 + rcx ]
add r11, r8
adc r9, 0x0
mov r10, r11
shrd r10, r9, 52
and r11, r12
mov [ rdi + 0x18 ], r11
mov r14, 0xffffffffffff 
and rbx, r14
lea rbx, [ rbx + r10 ]
mov [ rdi + 0x20 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2252
; seed 3106282983519293 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 682214 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=367, initial num_batches=31): 77307 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1133178152309979
; number reverted permutation / tried permutation: 75313 / 89835 =83.835%
; number reverted decision / tried decision: 67233 / 90164 =74.567%
; validated in 0.191s
