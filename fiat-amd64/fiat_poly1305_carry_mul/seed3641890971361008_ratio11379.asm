SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + rax]
lea r10, [r10 + 4 * r10]
mov rax, [ rdx + 0x8 ]
lea r11, [rax + rax]
lea r11, [r11 + 4 * r11]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r10
xor rdx, rdx
adox rcx, rbx
adox rbp, r8
mov r10, [ rax + 0x10 ]
lea r8, [r10 + 4 * r10]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r10, [ rax + 0x0 ]
mov rdx, r8
mov [ rsp - 0x70 ], r12
mulx r12, r8, [ rsi + 0x10 ]
adcx r8, r10
adcx rbx, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
shl r13, 0x1
add rcx, r9
adcx r11, rbp
mov rdx, [ rax + 0x0 ]
mulx rbp, r9, [ rsi + 0x10 ]
mov rdx, rcx
shrd rdx, r11, 44
add r8, r10
adcx r12, rbx
test al, al
adox r8, rdx
mov rbx, 0x0 
adox r12, rbx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, r13
mov rdx, [ rsi + 0x0 ]
mulx rbx, r13, [ rax + 0x10 ]
adcx r9, r10
adcx r11, rbp
test al, al
adox r9, r13
adox rbx, r11
mov rdx, r8
shrd rdx, r12, 43
test al, al
adox r9, rdx
mov rbp, 0x0 
adox rbx, rbp
mov r12, r9
shrd r12, rbx, 43
mov r10, 0x2c 
bzhi r13, rcx, r10
lea rcx, [r12 + 4 * r12]
lea r13, [ r13 + rcx ]
bzhi r11, r13, r10
mov rdx, 0x2b 
bzhi rbx, r8, rdx
shr r13, 44
lea r13, [ r13 + rbx ]
bzhi r8, r13, rdx
shr r13, 43
bzhi r12, r9, rdx
lea r13, [ r13 + r12 ]
mov [ rdi + 0x10 ], r13
mov [ rdi + 0x0 ], r11
mov [ rdi + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1379
; seed 3641890971361008 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3647 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=299, initial num_batches=31): 461 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.12640526460104196
; number reverted permutation / tried permutation: 433 / 510 =84.902%
; number reverted decision / tried decision: 301 / 489 =61.554%
; validated in 0.175s
