SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x0 ]
imul rdx, [ rax + 0x10 ], 0x5
mov rcx, [ rax + 0x10 ]
lea r8, [rcx + rcx]
lea r8, [r8 + 4 * r8]
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x78 ], rbp
shlx rbp, [ rax + 0x8 ], rdx
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, rcx
mov [ rsp - 0x68 ], r13
mulx r13, rcx, [ rsi + 0x10 ]
test al, al
adox r9, rbp
adox r12, rbx
imul rdx, [ rax + 0x8 ], 0xa
mulx rbp, rbx, [ rsi + 0x10 ]
add r9, r10
adcx r11, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r10, [ rax + 0x0 ]
test al, al
adox rcx, r10
adox r12, r13
mov rdx, r8
mulx r13, r8, [ rsi + 0x8 ]
adcx rbx, r8
adcx r13, rbp
mov rdx, [ rax + 0x0 ]
mulx r10, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, rbp
adox r10, r13
mov r8, rbx
shrd r8, r10, 44
mov rdx, [ rsi + 0x0 ]
mulx rbp, r13, [ rax + 0x8 ]
test al, al
adox rcx, r13
adox rbp, r12
adcx rcx, r8
adc rbp, 0x0
mov rdx, 0x7ffffffffff 
mov r12, rcx
and r12, rdx
shrd rcx, rbp, 43
test al, al
adox r9, rcx
mov r10, 0x0 
adox r11, r10
mov r8, r9
shrd r8, r11, 43
lea r13, [r8 + 4 * r8]
mov rbp, 0xfffffffffff 
and rbx, rbp
lea rbx, [ rbx + r13 ]
mov rcx, rbx
shr rcx, 44
lea rcx, [ rcx + r12 ]
and rbx, rbp
and r9, rdx
mov r12, rcx
shr r12, 43
lea r12, [ r12 + r9 ]
mov [ rdi + 0x10 ], r12
and rcx, rdx
mov [ rdi + 0x8 ], rcx
mov [ rdi + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0905
; seed 1022659676860625 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2345 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=493, initial num_batches=31): 399 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1701492537313433
; number reverted permutation / tried permutation: 418 / 511 =81.800%
; number reverted decision / tried decision: 340 / 488 =69.672%
; validated in 0.133s
