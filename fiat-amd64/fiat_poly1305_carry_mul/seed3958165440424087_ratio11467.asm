SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ r10 + 0x8 ]
lea r8, [rdx + rdx]
mov rdx, [ r10 + 0x10 ]
lea r9, [rdx + 4 * rdx]
imul rdx, [ r10 + 0x10 ], 0xa
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, rax
mov [ rsp - 0x70 ], r12
mulx r12, rax, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, rbx
adox rbp, r12
mov rdx, [ r10 + 0x0 ]
mulx r12, rbx, [ rsi + 0x0 ]
adcx rax, rbx
adcx r12, rbp
mov rdx, r9
mulx rbp, r9, [ rsi + 0x10 ]
test al, al
adox r9, r11
adox rcx, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbx, r11, [ r10 + 0x8 ]
mov rdx, r8
mulx rbp, r8, [ rsi + 0x8 ]
adcx r9, r11
adcx rbx, rcx
mov rdx, [ rsi + 0x10 ]
mulx r11, rcx, [ r10 + 0x0 ]
test al, al
adox rcx, r8
adox rbp, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r8, [ r10 + 0x10 ]
adcx rcx, r8
adcx r11, rbp
mov rdx, rax
shrd rdx, r12, 44
xor r12, r12
adox r9, rdx
adox rbx, r12
mov rbp, r9
shrd rbp, rbx, 43
add rcx, rbp
adc r11, 0x0
mov r8, 0x7ffffffffff 
and r9, r8
mov rdx, rcx
shrd rdx, r11, 43
imul rbx, rdx, 0x5
mov rbp, 0xfffffffffff 
and rax, rbp
lea rax, [ rax + rbx ]
mov r11, rax
shr r11, 44
lea r11, [ r11 + r9 ]
and rax, rbp
mov r9, r11
and r9, r8
shr r11, 43
and rcx, r8
mov [ rdi + 0x8 ], r9
lea r11, [ r11 + rcx ]
mov [ rdi + 0x0 ], rax
mov [ rdi + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1467
; seed 3958165440424087 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3312 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=548, initial num_batches=31): 416 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.12560386473429952
; number reverted permutation / tried permutation: 374 / 508 =73.622%
; number reverted decision / tried decision: 312 / 491 =63.544%
; validated in 0.13s
