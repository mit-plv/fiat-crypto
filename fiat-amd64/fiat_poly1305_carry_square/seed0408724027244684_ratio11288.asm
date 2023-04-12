SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, rax
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
add rax, r11
adcx rcx, r10
mov rdx, rax
shrd rdx, rcx, 44
mov r8, [ rsi + 0x8 ]
lea r9, [r8 + r8]
mov r8, [ rsi + 0x10 ]
lea r10, [r8 + 4 * r8]
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, r10
mov rdx, r9
mulx r10, r9, [ rsi + 0x0 ]
test al, al
adox r11, r9
adox r10, rcx
adcx r11, r8
adc r10, 0x0
mov r8, r11
shrd r8, r10, 43
mov rcx, [ rsi + 0x10 ]
lea r9, [rcx + rcx]
mov rcx, 0x7ffffffffff 
and r11, rcx
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, r9
mov [ rsp - 0x78 ], rbp
mulx rbp, r9, [ rsi + 0x0 ]
adox r10, r9
adox rbp, rbx
adcx r10, r8
adc rbp, 0x0
mov r8, r10
shrd r8, rbp, 43
lea rdx, [r8 + 4 * r8]
and r10, rcx
mov rbx, 0xfffffffffff 
and rax, rbx
lea rax, [ rax + rdx ]
mov r9, rax
shr r9, 44
lea r9, [ r9 + r11 ]
mov r11, r9
shr r11, 43
lea r11, [ r11 + r10 ]
mov [ rdi + 0x10 ], r11
and r9, rcx
and rax, rbx
mov [ rdi + 0x8 ], r9
mov [ rdi + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1288
; seed 0408724027244684 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1881 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=617, initial num_batches=31): 357 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.189792663476874
; number reverted permutation / tried permutation: 370 / 493 =75.051%
; number reverted decision / tried decision: 347 / 506 =68.577%
; validated in 0.103s
