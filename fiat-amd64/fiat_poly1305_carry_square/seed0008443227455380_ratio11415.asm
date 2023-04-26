SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, rdx
mov rdx, [ rsi + 0x8 ]
lea rcx, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rax
imul rdx, [ rsi + 0x10 ], 0x5
xor rax, rax
adox r8, r10
adox r11, r9
mulx r9, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, rcx
mov rdx, r8
shrd rdx, r11, 44
test al, al
adox r10, rax
adox rbx, r9
adcx r10, rdx
adc rbx, 0x0
mov r11, r10
shrd r11, rbx, 43
imul r9, [ rsi + 0x10 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx rbx, rax, r9
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x8 ]
add rcx, rax
adcx rbx, r9
xor rdx, rdx
adox rcx, r11
adox rbx, rdx
mov r11, rcx
shrd r11, rbx, 43
mov rax, 0xfffffffffff 
and r8, rax
lea r9, [r11 + 4 * r11]
lea r8, [ r8 + r9 ]
mov rbx, r8
shr rbx, 44
mov r11, 0x2b 
bzhi r9, r10, r11
lea rbx, [ rbx + r9 ]
bzhi r10, rbx, r11
and r8, rax
mov [ rdi + 0x8 ], r10
bzhi r9, rcx, r11
shr rbx, 43
lea rbx, [ rbx + r9 ]
mov [ rdi + 0x0 ], r8
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.1415
; seed 0008443227455380 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3111 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1073, initial num_batches=31): 774 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.24879459980713597
; number reverted permutation / tried permutation: 420 / 503 =83.499%
; number reverted decision / tried decision: 347 / 496 =69.960%
; validated in 0.171s
