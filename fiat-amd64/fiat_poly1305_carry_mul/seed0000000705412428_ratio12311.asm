SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 4 * rax]
imul rax, [ rdx + 0x10 ], 0xa
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ r11 + 0x0 ]
mov rdx, r10
mulx r9, r10, [ rsi + 0x10 ]
imul rdx, [ r11 + 0x8 ], 0xa
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, rcx
adox r8, r9
mov rdx, rax
mulx rcx, rax, [ rsi + 0x8 ]
adcx rbx, rax
adcx rcx, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ r11 + 0x0 ]
add rbx, r9
adcx rbp, rcx
mov rdx, [ r11 + 0x8 ]
mulx rcx, rax, [ rsi + 0x0 ]
mov rdx, rbx
shrd rdx, rbp, 44
xor r9, r9
adox r10, rax
adox rcx, r8
adcx r10, rdx
adc rcx, 0x0
mov r8, r10
shrd r8, rcx, 43
mov rdx, [ rsi + 0x10 ]
mulx rax, rbp, [ r11 + 0x0 ]
imul rdx, [ r11 + 0x8 ], 0x2
mulx r9, rcx, [ rsi + 0x8 ]
xor rdx, rdx
adox rbp, rcx
adox r9, rax
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, [ r11 + 0x10 ]
adcx rbp, rax
adcx rcx, r9
add rbp, r8
adc rcx, 0x0
mov rdx, rbp
shrd rdx, rcx, 43
lea r8, [rdx + 4 * rdx]
mov r9, 0xfffffffffff 
and rbx, r9
lea rbx, [ rbx + r8 ]
mov rax, 0x7ffffffffff 
and r10, rax
mov rcx, rbx
shr rcx, 44
lea rcx, [ rcx + r10 ]
mov rdx, rcx
and rdx, rax
and rbp, rax
shr rcx, 43
and rbx, r9
lea rcx, [ rcx + rbp ]
mov [ rdi + 0x0 ], rbx
mov [ rdi + 0x10 ], rcx
mov [ rdi + 0x8 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2311
; seed 2099772398771274 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 310430 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=946, initial num_batches=31): 69517 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.22393776374706054
; number reverted permutation / tried permutation: 72553 / 89565 =81.006%
; number reverted decision / tried decision: 69559 / 90434 =76.917%
; validated in 0.087s
