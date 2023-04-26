SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 480
mov rax, [ rsi + 0x38 ]
mov r10, rax
shl r10, 0x2
mov rdx, [ rsi + 0x0 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x20 ]
lea rcx, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov r8, rdx
shl r8, 0x1
mov rdx, 0x1 
shlx r9, [ rsi + 0x40 ], rdx
mov rdx, rcx
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x38 ]
mov [ rsp - 0x70 ], r12
mov r12, rbp
shl r12, 0x1
xchg rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x38 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
mov rdx, 0x2 
mov [ rsp - 0x48 ], r9
shlx r9, [ rsi + 0x30 ], rdx
mov rdx, r9
mov [ rsp - 0x40 ], rdi
mulx rdi, r9, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r15
mov r15, 0x1 
mov [ rsp - 0x30 ], rdi
shlx rdi, [ rsi + 0x30 ], r15
imul r15, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x28 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], r8
mulx r8, r9, rdx
mov rdx, 0x2 
mov [ rsp - 0x10 ], r8
shlx r8, [ rsi + 0x40 ], rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r13
mulx r13, r9, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], rbp
mulx rbp, r9, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r9
mulx r9, rbp, r8
mov rdx, r13
mov [ rsp + 0x30 ], r11
mulx r11, r13, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], rax
mulx rax, r13, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r9
mov [ rsp + 0x58 ], rbp
mulx rbp, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], rcx
mulx rcx, rbx, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], rbx
mulx rbx, rcx, r15
add r13, r9
adcx rbp, rax
mov rdx, r10
mulx rax, r10, [ rsi + 0x30 ]
mov [ rsp + 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rcx
imul rcx, [ rsi + 0x28 ], 0x4
mov [ rsp + 0x90 ], rbx
xor rbx, rbx
adox r13, [ rsp + 0x68 ]
adox rbp, [ rsp + 0x60 ]
adcx r10, [ rsp + 0x58 ]
adcx rax, [ rsp + 0x50 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], r13
mulx r13, rbp, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], rax
mulx rax, r15, rcx
xor rdx, rdx
adox r15, rbp
adox r13, rax
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], r10
mulx r10, rax, r8
adcx r15, r9
adcx r13, [ rsp + 0x90 ]
xor rdx, rdx
adox r15, rcx
adox rbp, r13
adcx r15, [ rsp + 0x48 ]
adcx rbp, [ rsp + 0x30 ]
mov r9, 0x1 
shlx rcx, [ rsi + 0x28 ], r9
mov r13, rax
xor r9, r9
adox r13, [ rsp + 0x18 ]
adox r10, [ rsp + 0x0 ]
mov rdx, r15
shrd rdx, rbp, 58
shr rbp, 58
xchg rdx, rcx
mulx r9, rax, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r13
mov [ rsp + 0xc8 ], r12
mulx r12, r13, rbx
mov rdx, r10
mov [ rsp + 0xd0 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
test al, al
adox rax, [ rsp + 0x88 ]
adox r9, [ rsp + 0x80 ]
adcx rax, r13
adcx r12, r9
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], rbp
mulx rbp, r9, r8
test al, al
adox rax, r9
adox rbp, r12
mov rdx, [ rsp - 0x18 ]
mulx r9, r12, [ rsi + 0x0 ]
adcx rax, r12
adcx r9, rbp
mov rdx, 0x3ffffffffffffff 
and r15, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, rbp, rbx
mov rdx, rbp
adox rdx, [ rsp - 0x20 ]
adox r12, [ rsp - 0x30 ]
adcx rax, rcx
adcx r9, [ rsp + 0xd0 ]
xchg rdx, r8
mulx rbp, rcx, [ rsi + 0x18 ]
xchg rdx, rdi
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], r10
mulx r10, r15, [ rsi + 0x30 ]
mov rdx, rax
shrd rdx, r9, 58
shr r9, 58
mov [ rsp + 0xf0 ], r14
xor r14, r14
adox r8, rcx
adox rbp, r12
xchg rdx, rbx
mulx rcx, r12, [ rsi + 0x28 ]
adcx r15, r12
adcx rcx, r10
mov rdx, [ rsp - 0x28 ]
mulx r12, r10, [ rsi + 0x0 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], rbx
mulx rbx, r9, rdi
add r15, r9
adcx rbx, rcx
test al, al
adox r8, [ rsp - 0x38 ]
adox rbp, [ rsp - 0x40 ]
mov rdx, r14
mulx rdi, r14, [ rsi + 0x8 ]
adcx r8, r10
adcx r12, rbp
add r15, r14
adcx rdi, rbx
add r8, [ rsp + 0x100 ]
adcx r12, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, r11
mov rdx, [ rsp - 0x8 ]
mov r9, rdx
test al, al
adox r9, [ rsp + 0xb0 ]
mov rbx, [ rsp - 0x10 ]
adox rbx, [ rsp + 0xa8 ]
mov rdx, r8
shrd rdx, r12, 58
shr r12, 58
add r9, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0x38 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r12
mulx r12, r14, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], rbx
mulx rbx, rbp, [ rsp + 0xc8 ]
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], rbp
mulx rbp, rbx, [ rsi + 0x40 ]
mov [ rsp + 0x130 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], rbx
mov [ rsp + 0x140 ], r9
mulx r9, rbx, r11
test al, al
adox r15, rcx
adox r10, rdi
mov rdx, r13
mulx r11, r13, [ rsi + 0x0 ]
mov rdi, rbx
adcx rdi, [ rsp + 0xc0 ]
adcx r9, [ rsp + 0xb8 ]
mov rcx, r14
add rcx, [ rsp + 0x140 ]
adcx r12, [ rsp + 0x118 ]
add rdi, [ rsp + 0x128 ]
adcx r9, [ rsp + 0x120 ]
test al, al
adox rdi, r13
adox r11, r9
mov r14, rdx
mov rdx, [ rsp + 0xc8 ]
mulx r13, rbx, [ rsi + 0x18 ]
adcx r15, [ rsp + 0x110 ]
adcx r10, [ rsp + 0x108 ]
mov rdx, 0x3a 
bzhi r9, r15, rdx
shrd r15, r10, 58
shr r10, 58
mov rdx, rbx
mov [ rsp + 0x148 ], r9
xor r9, r9
adox rdx, [ rsp + 0x138 ]
adox r13, [ rsp + 0x130 ]
adcx rcx, r15
adcx r10, r12
mov r12, rcx
shrd r12, r10, 58
shr r10, 58
add rdi, r12
adcx r10, r11
mov r11, [ rsp + 0x148 ]
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, r15, rdx
mov rdx, r14
mulx r9, r14, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
add r11, rbx
adcx r12, r13
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, [ rsp + 0xf0 ]
mov rdx, r14
add rdx, [ rsp + 0xa0 ]
adcx r9, [ rsp + 0x98 ]
xor r14, r14
adox r11, [ rsp + 0x78 ]
adox r12, [ rsp + 0x70 ]
mov r14, 0x3ffffffffffffff 
mov [ rsp + 0x158 ], r12
mov r12, rdi
and r12, r14
adox rdx, [ rsp + 0x28 ]
adox r9, [ rsp + 0x20 ]
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x28 ], r12
adcx r15, [ rsp + 0xe8 ]
mov r12, [ rsp + 0xd8 ]
adcx r12, [ rsp + 0x150 ]
test al, al
adox r15, [ rsp + 0x10 ]
adox r12, [ rsp + 0x8 ]
shrd rdi, r10, 58
shr r10, 58
test al, al
adox r15, r13
adox rbx, r12
adcx rdx, rdi
adcx r10, r9
mov r13, rdx
mov rdx, [ rsp + 0xf0 ]
mulx r12, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r14, rdi, rbp
mov rdx, r13
shrd rdx, r10, 58
shr r10, 58
add r11, r9
adcx r12, [ rsp + 0x158 ]
xor rbp, rbp
adox r11, rdx
adox r10, r12
mov r9, r11
shrd r9, r10, 58
shr r10, 58
mov rdx, 0x3ffffffffffffff 
and r13, rdx
and r11, rdx
adox r15, rdi
adox r14, rbx
adcx r15, r9
adcx r10, r14
mov rbx, 0x39 
bzhi rdi, r15, rbx
shrd r15, r10, 57
shr r10, 57
xor r12, r12
adox r15, [ rsp + 0xe0 ]
adox r10, r12
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x40 ], rdi
mov [ rbp + 0x38 ], r11
mov r9, r15
and r9, rdx
mov [ rbp + 0x0 ], r9
and r8, rdx
and rax, rdx
shrd r15, r10, 58
lea r15, [ r15 + rax ]
mov r11, r15
and r11, rdx
mov [ rbp + 0x8 ], r11
shr r15, 58
and rcx, rdx
mov [ rbp + 0x20 ], rcx
mov [ rbp + 0x30 ], r13
lea r15, [ r15 + r8 ]
mov [ rbp + 0x10 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 480
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0320
; seed 1345640111325824 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5411238 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=69, initial num_batches=31): 184032 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03400922302807601
; number reverted permutation / tried permutation: 62671 / 89993 =69.640%
; number reverted decision / tried decision: 49115 / 90006 =54.569%
; validated in 2.386s
