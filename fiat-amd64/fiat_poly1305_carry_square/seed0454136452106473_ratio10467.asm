SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x8 ]
lea r11, [rax + rax]
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, rax
mulx rcx, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
xor rdx, rdx
adox rax, r8
adox r9, rcx
mov rcx, [ rsi + 0x10 ]
lea r8, [rcx + 4 * rcx]
mov rdx, r8
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, r11
mov [ rsp - 0x80 ], rbx
mulx rbx, r11, [ rsi + 0x0 ]
adcx rcx, r11
adcx rbx, r8
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, r10
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, r10
adox rbp, r11
mov r11, rax
shrd r11, r9, 44
mov r9, 0xfffffffffff 
and rax, r9
adox rcx, r11
adox rbx, rdx
mov r10, rcx
shrd r10, rbx, 43
add r8, r10
adc rbp, 0x0
mov r11, r8
shrd r11, rbp, 43
lea rbx, [r11 + 4 * r11]
lea rax, [ rax + rbx ]
mov r10, rax
shr r10, 44
mov rbp, 0x7ffffffffff 
and rcx, rbp
lea r10, [ r10 + rcx ]
mov r11, r10
shr r11, 43
and r10, rbp
and r8, rbp
lea r11, [ r11 + r8 ]
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x8 ], r10
and rax, r9
mov [ rdi + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0467
; seed 0454136452106473 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1573 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=619, initial num_batches=31): 292 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1856325492689129
; number reverted permutation / tried permutation: 443 / 524 =84.542%
; number reverted decision / tried decision: 352 / 475 =74.105%
; validated in 0.081s
