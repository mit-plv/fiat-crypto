SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, rax
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
lea r9, [rdx + 8 * rdx]
lea rbx, [rdx + 2 * r9]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r9, rbx
imul rdx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rax
mov rdx, 0x1 
mov [ rsp - 0x58 ], r15
shlx r15, [ rsi + 0x10 ], rdx
xor rdx, rdx
adox r13, rcx
adox r8, r14
mov rcx, [ rsi + 0x20 ]
lea r14, [rcx + 8 * rcx]
lea rdx, [rcx + 2 * r14]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r8
lea r8, [rdx + rdx]
adcx r9, r10
adcx r11, rbp
mov rdx, [ rsi + 0x8 ]
mov r10, rdx
shl r10, 0x1
mov rdx, rax
mulx rbp, rax, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, rax
adox rbp, r12
mov rdx, [ rsi + 0x0 ]
mulx rax, r12, rdx
mov rdx, r10
mov [ rsp - 0x40 ], r8
mulx r8, r10, [ rsi + 0x0 ]
adcx rbx, r12
adcx rax, rbp
mov rdx, rbx
shrd rdx, rax, 51
xor rbp, rbp
adox r9, r10
adox r8, r11
adcx r9, rdx
adc r8, 0x0
mov r11, [ rsi + 0x18 ]
lea r12, [r11 + r11]
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, r12
mov rdx, r9
shrd rdx, r8, 51
xchg rdx, rcx
mulx r8, rax, [ rsi + 0x20 ]
mov rdx, r15
mulx rbp, r15, [ rsi + 0x8 ]
xor rdx, rdx
adox rax, r15
adox rbp, r8
adcx r13, r14
adcx rdi, [ rsp - 0x48 ]
test al, al
adox r13, rcx
adox rdi, rdx
adcx rax, r11
adcx r10, rbp
mov r14, 0x7ffffffffffff 
and r9, r14
mov r11, r13
and r11, r14
shrd r13, rdi, 51
test al, al
adox rax, r13
adox r10, rdx
mov rcx, rax
shrd rcx, r10, 51
mov rdx, r12
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, r15, rdx
add r15, r12
adcx r8, rbp
mov rdx, [ rsp - 0x40 ]
mulx r13, rdi, [ rsi + 0x0 ]
test al, al
adox r15, rdi
adox r13, r8
adcx r15, rcx
adc r13, 0x0
mov rdx, r15
shrd rdx, r13, 51
imul r10, rdx, 0x13
and rbx, r14
lea rbx, [ rbx + r10 ]
mov rcx, rbx
shr rcx, 51
lea rcx, [ rcx + r9 ]
mov r9, rcx
shr r9, 51
and rcx, r14
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rcx
lea r9, [ r9 + r11 ]
mov [ r12 + 0x10 ], r9
and rbx, r14
and r15, r14
mov [ r12 + 0x20 ], r15
and rax, r14
mov [ r12 + 0x18 ], rax
mov [ r12 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.2162
; seed 2777644898954146 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 514218 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=265, initial num_batches=31): 58948 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11463620487808672
; number reverted permutation / tried permutation: 75825 / 90282 =83.987%
; number reverted decision / tried decision: 64819 / 89717 =72.248%
; validated in 0.2s
