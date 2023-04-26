SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 256
mov rax, 0x2 
shlx r10, [ rsi + 0x40 ], rax
imul r11, [ rsi + 0x30 ], 0x2
imul rdx, [ rsi + 0x18 ], 0x2
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mulx rax, r15, rcx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r12
mulx r12, r13, r11
mov rdx, [ rsi + 0x40 ]
mov [ rsp - 0x30 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x28 ], r13
lea r13, [ 4 * rdx]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], rbp
mulx rbp, r12, r13
mov rdx, rcx
mov [ rsp - 0x10 ], rax
mulx rax, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x8 ], rax
lea rax, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x0 ], rcx
lea rcx, [ 4 * rdx]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], rax
mov [ rsp + 0x10 ], r15
mulx r15, rax, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], rax
mulx rax, r15, rcx
imul rdx, [ rsi + 0x28 ], 0x4
test al, al
adox r12, r15
adox rax, rbp
mulx r15, rbp, [ rsi + 0x20 ]
mov rdx, rcx
mov [ rsp + 0x28 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
adcx rdi, rcx
adcx r15, r14
mulx rcx, r14, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rcx
mov rcx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], r14
mov r14, rcx
shl r14, 0x1
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], rax
mulx rax, rbp, r10
test al, al
adox rdi, r8
adox r9, r15
mov rdx, r14
mulx r8, r14, [ rsi + 0x28 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r9
mov [ rsp + 0x58 ], rdi
mulx rdi, r9, r13
adcx r12, rbp
adcx rax, [ rsp + 0x48 ]
xor rdx, rdx
adox r14, r9
adox rdi, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, r13
mov rdx, 0x1 
shlx r13, [ rsi + 0x8 ], rdx
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x10 ]
mov rdx, rbp
adcx rdx, [ rsp + 0x40 ]
adcx r8, [ rsp + 0x28 ]
add rdx, rcx
adcx r9, r8
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, r13
mov rdx, r10
mulx r13, r10, [ rsi + 0x8 ]
test al, al
adox rbp, r10
adox r13, r9
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], rbx
mulx rbx, r10, rdx
adcx rbp, r10
adcx rbx, r13
xor rdx, rdx
adox r14, [ rsp + 0x38 ]
adox rdi, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r13, r9
adcx r14, r13
adcx r10, rdi
mov rdx, [ rsi + 0x8 ]
mulx r13, rdi, rdx
test al, al
adox r12, rdi
adox r13, rax
adcx r14, rcx
adcx r8, r10
imul rdx, [ rsi + 0x10 ], 0x2
mov rax, rbp
shrd rax, rbx, 58
shr rbx, 58
add r14, rax
adcx rbx, r8
mulx r10, rcx, [ rsi + 0x8 ]
mov rdi, r14
shrd rdi, rbx, 58
shr rbx, 58
mulx rax, r8, [ rsi + 0x0 ]
test al, al
adox r12, r8
adox rax, r13
adcx r12, rdi
adcx rbx, rax
mov r13, 0x3ffffffffffffff 
and rbp, r13
mov rdx, rcx
adox rdx, [ rsp + 0x58 ]
adox r10, [ rsp + 0x50 ]
mov rcx, r12
shrd rcx, rbx, 58
shr rbx, 58
and r14, r13
adox rdx, [ rsp + 0x10 ]
adox r10, [ rsp - 0x10 ]
adcx rdx, rcx
adcx rbx, r10
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mulx rax, r8, r9
mov rdx, r8
add rdx, [ rsp + 0x20 ]
adcx rax, [ rsp + 0x18 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r14
mulx r14, r13, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], rbp
mov [ rsp + 0x78 ], r11
mulx r11, rbp, r9
xor rdx, rdx
adox rcx, r10
adox r8, rax
mov rdx, [ rsi + 0x38 ]
mulx r10, rax, [ rsp + 0x8 ]
adcx rax, rbp
adcx r11, r10
xor rdx, rdx
adox rcx, [ rsp - 0x18 ]
adox r8, [ rsp - 0x38 ]
adcx rcx, r13
adcx r14, r8
mov r13, rdi
shrd r13, rbx, 58
shr rbx, 58
test al, al
adox rcx, r13
adox rbx, r14
mov rdx, [ rsi + 0x0 ]
mulx r10, rbp, r15
mov rdx, [ rsi + 0x38 ]
mulx r14, r8, r9
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, rdx
adcx r8, r9
adcx r13, r14
mov rdx, [ rsi + 0x10 ]
mulx r9, r14, [ rsp + 0x60 ]
add r8, r14
adcx r9, r13
xor rdx, rdx
adox rax, [ rsp + 0x0 ]
adox r11, [ rsp - 0x8 ]
mov r13, rcx
shrd r13, rbx, 58
shr rbx, 58
add rax, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
add rax, rbp
adcx r10, r11
add rax, r13
adcx rbx, r10
mov rdx, [ rsi + 0x8 ]
mulx r14, rbp, r15
mov rdx, [ rsi + 0x10 ]
mulx r11, r13, r15
test al, al
adox r8, rbp
adox r14, r9
mov rdx, 0x3ffffffffffffff 
and rcx, rdx
mov r9, rax
shrd r9, rbx, 58
shr rbx, 58
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x20 ], rcx
mov rdx, [ rsp + 0x78 ]
mulx rcx, rbp, [ rsi + 0x0 ]
test al, al
adox r8, rbp
adox rcx, r14
mov r14, 0x3a 
bzhi rbp, rax, r14
mov [ r10 + 0x28 ], rbp
adox r8, r9
adox rbx, rcx
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, [ rsp + 0x60 ]
bzhi rdx, r8, r14
mov rbp, rdx
mov rdx, [ rsi + 0x40 ]
mulx r10, r14, [ rsp - 0x20 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], rbp
shrd r8, rbx, 58
shr rbx, 58
add r14, r9
adcx rcx, r10
test al, al
adox r14, r13
adox r11, rcx
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r9, rdx
mov rdx, r15
mulx r10, r15, [ rsi + 0x18 ]
adcx r14, [ rsp - 0x28 ]
adcx r11, [ rsp - 0x30 ]
xor rdx, rdx
adox r9, r15
adox r10, rbp
mov rdx, rax
mulx rcx, rax, [ rsi + 0x10 ]
adcx r9, rax
adcx rcx, r10
mov rdx, [ rsi + 0x0 ]
mulx r15, rbp, [ rsp + 0x8 ]
add r14, rbp
adcx r15, r11
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rsp - 0x20 ]
mov rdx, [ rsp + 0x8 ]
mulx rbp, rax, [ rsi + 0x8 ]
test al, al
adox r14, r8
adox rbx, r15
mov rdx, 0x3a 
bzhi r8, r14, rdx
adox r9, rax
adox rbp, rcx
xor rcx, rcx
adox r9, r11
adox r10, rbp
mov [ r13 + 0x38 ], r8
shrd r14, rbx, 58
shr rbx, 58
xor r15, r15
adox r9, r14
adox rbx, r10
mov rcx, 0x1ffffffffffffff 
mov r11, r9
and r11, rcx
shrd r9, rbx, 57
shr rbx, 57
xor rax, rax
adox r9, [ rsp + 0x70 ]
adox rbx, rax
bzhi r15, rdi, rdx
mov rdi, r9
shrd rdi, rbx, 58
bzhi r8, r12, rdx
bzhi r12, r9, rdx
add rdi, [ rsp + 0x68 ]
bzhi rbp, rdi, rdx
mov [ r13 + 0x8 ], rbp
shr rdi, 58
mov [ r13 + 0x18 ], r15
lea rdi, [ rdi + r8 ]
mov [ r13 + 0x10 ], rdi
mov [ r13 + 0x40 ], r11
mov [ r13 + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 256
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4749
; seed 2320109875325491 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3154610 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=78, initial num_batches=31): 105260 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.03336704061674819
; number reverted permutation / tried permutation: 67313 / 90106 =74.704%
; number reverted decision / tried decision: 61708 / 89893 =68.646%
; validated in 2.068s
