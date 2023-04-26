SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
mov r10, rax
shl r10, 0x1
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
lea r8, [rdx + 4 * rdx]
mov rdx, rax
mulx r9, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
shl rbx, 0x1
xor rdx, rdx
adox rax, r11
adox rcx, r9
mov rdx, r8
mulx r11, r8, [ rsi + 0x10 ]
mov rdx, rbx
mulx r9, rbx, [ rsi + 0x0 ]
adcx r8, rbx
adcx r9, r11
xchg rdx, r10
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, rax
shrd rdx, rcx, 44
xor rcx, rcx
adox r8, rdx
adox r9, rcx
mov rdx, r10
mulx rcx, r10, [ rsi + 0x8 ]
adcx r10, r11
adcx rbx, rcx
mov rdx, r8
shrd rdx, r9, 43
mov r11, 0x7ffffffffff 
and r8, r11
adox r10, rdx
mov r9, 0x0 
adox rbx, r9
mov rcx, r10
shrd rcx, rbx, 43
and r10, r11
mov rdx, 0xfffffffffff 
and rax, rdx
lea rbx, [rcx + 4 * rcx]
lea rax, [ rax + rbx ]
mov rcx, rax
and rcx, rdx
mov [ rdi + 0x0 ], rcx
shr rax, 44
lea rax, [ rax + r8 ]
mov r8, rax
shr r8, 43
lea r8, [ r8 + r10 ]
mov [ rdi + 0x10 ], r8
and rax, r11
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0353
; seed 1363716877730036 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3839 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=406, initial num_batches=31): 416 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.10836155248762698
; number reverted permutation / tried permutation: 443 / 511 =86.693%
; number reverted decision / tried decision: 315 / 488 =64.549%
; validated in 0.132s
