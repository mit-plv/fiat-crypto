SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x8 ]
lea rdx, [r11 + r11]
imul r11, [ rsi + 0x10 ], 0x14
xchg rdx, r11
mulx r8, rcx, [ rsi + 0x8 ]
test al, al
adox rcx, rax
adox r10, r8
imul r9, [ rsi + 0x10 ], 0x5
mov rax, rcx
shrd rax, r10, 44
mov rdx, 0xfffffffffff 
and rcx, rdx
mov rdx, r9
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, r11
adox r9, r10
adox rbx, r8
adcx r9, rax
adc rbx, 0x0
mov rdx, 0x7ffffffffff 
mov rax, r9
and rax, rdx
shrd r9, rbx, 43
mov r8, [ rsi + 0x10 ]
mov r10, r8
shl r10, 0x1
mov rdx, [ rsi + 0x8 ]
mulx rbx, r8, r11
mov rdx, r10
mulx r11, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, r10
adox r11, rbx
adcx r8, r9
adc r11, 0x0
mov r9, r8
shrd r9, r11, 43
mov rbx, 0x7ffffffffff 
and r8, rbx
lea r10, [r9 + 4 * r9]
lea rcx, [ rcx + r10 ]
mov r11, rcx
shr r11, 44
mov r9, 0xfffffffffff 
and rcx, r9
lea r11, [ r11 + rax ]
mov [ rdi + 0x0 ], rcx
mov rax, r11
and rax, rbx
shr r11, 43
lea r11, [ r11 + r8 ]
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0777
; seed 0358857798588660 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1460 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=623, initial num_batches=31): 293 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.20068493150684932
; number reverted permutation / tried permutation: 410 / 505 =81.188%
; number reverted decision / tried decision: 362 / 494 =73.279%
; validated in 0.082s
