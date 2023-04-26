SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 456
mov rax, [ rdx + 0x18 ]
lea r10, [rax + rax]
mov rax, 0x1 
shlx r11, [ rdx + 0x20 ], rax
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rcx + 0x0 ]
mov rdx, [ rcx + 0x10 ]
mov rax, rdx
shl rax, 0x1
mov rdx, [ rcx + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rcx + 0x28 ]
mov rdx, r11
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r15
mov r15, rdx
mov rdx, [ rcx + 0x10 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rbp
mulx rbp, r14, [ rsi + 0x20 ]
imul rdx, [ rcx + 0x30 ], 0x2
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], rbp
mulx rbp, rbx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], r14
mov r14, rdx
mov rdx, [ rcx + 0x0 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r8
mulx r8, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r9
mulx r9, r8, [ rcx + 0x8 ]
mov rdx, [ rcx + 0x40 ]
mov [ rsp + 0x8 ], r9
lea r9, [rdx + rdx]
mov rdx, [ rcx + 0x8 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], r8
mulx r8, rdi, r15
imul rdx, [ rcx + 0x28 ], 0x2
mov [ rsp + 0x30 ], r11
mov [ rsp + 0x38 ], r13
mulx r13, r11, [ rsi + 0x30 ]
mov [ rsp + 0x40 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], r11
mulx r11, r13, [ rcx + 0x18 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], r13
mulx r13, r11, r15
imul rdx, [ rcx + 0x38 ], 0x2
mov [ rsp + 0x68 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], r9
mulx r9, rdi, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r8
mov [ rsp + 0x88 ], rax
mulx rax, r8, [ rcx + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x90 ], rax
mov [ rsp + 0x98 ], r8
mulx r8, rax, [ rcx + 0x0 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xa0 ], r8
mov [ rsp + 0xa8 ], rax
mulx rax, r8, r10
test al, al
adox r11, rdi
adox r9, r13
mov rdx, [ rsi + 0x30 ]
mulx rdi, r13, r15
adcx r11, rbx
adcx rbp, r9
mov rdx, [ rsi + 0x40 ]
mulx rbx, r15, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xb0 ], rbp
mulx rbp, r9, [ rsp + 0x78 ]
add r15, r8
adcx rax, rbx
add r15, r13
adcx rdi, rax
mov rdx, [ rcx + 0x0 ]
mulx r13, r8, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x40 ]
mulx rax, rbx, r10
add r9, r8
adcx r13, rbp
add rbx, [ rsp + 0x70 ]
adcx rax, [ rsp + 0x68 ]
mov rdx, [ rcx + 0x8 ]
mulx rbp, r10, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0xb8 ], r11
mulx r11, r8, [ rsi + 0x38 ]
xor rdx, rdx
adox r9, r10
adox rbp, r13
adcx rbx, [ rsp + 0x50 ]
adcx rax, [ rsp + 0x48 ]
mov r13, 0x1 
shlx r10, [ rcx + 0x8 ], r13
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc0 ], rbp
mulx rbp, r13, r14
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], rax
mulx rax, r9, r10
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xd8 ], rbx
mulx rbx, r10, r12
test al, al
adox r9, r8
adox r11, rax
mov rdx, [ rsi + 0x28 ]
mulx rax, r8, [ rsp + 0x78 ]
adcx r10, r13
adcx rbp, rbx
mov rdx, [ rsi + 0x30 ]
mulx rbx, r13, [ rsp + 0x80 ]
add r10, r13
adcx rbx, rbp
mov rdx, [ rsi + 0x20 ]
mulx r13, rbp, r12
xor rdx, rdx
adox r10, r8
adox rax, rbx
adcx r9, [ rsp + 0x40 ]
adcx r11, [ rsp + 0x38 ]
add r9, [ rsp + 0x30 ]
adcx r11, [ rsp + 0x18 ]
add r10, [ rsp - 0x10 ]
adcx rax, [ rsp - 0x18 ]
mov rdx, [ rcx + 0x8 ]
mulx rbx, r8, [ rsi + 0x18 ]
add r10, r8
adcx rbx, rax
mov rdx, [ rsi + 0x28 ]
mulx r8, rax, r12
xor rdx, rdx
adox r9, rbp
adox r13, r11
mov rdx, [ rsi + 0x18 ]
mulx rbp, r12, r14
adcx r9, r12
adcx rbp, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, [ rcx + 0x10 ]
mov rdx, [ rcx + 0x18 ]
mov [ rsp + 0xe0 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
test al, al
adox r10, r11
adox r13, rbx
mov rdx, r14
mulx rbx, r14, [ rsi + 0x20 ]
adcx r10, r12
adcx rbp, r13
add r15, rax
adcx r8, rdi
test al, al
adox r15, r14
adox rbx, r8
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, [ rsp + 0x80 ]
adcx r15, rax
adcx r11, rbx
mov rdx, [ rsi + 0x0 ]
mulx r13, r12, [ rcx + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r14, [ rsp + 0x78 ]
mov rdx, [ rsp + 0x80 ]
mulx rax, rbx, [ rsi + 0x10 ]
add r9, rbx
adcx rax, [ rsp + 0xe0 ]
test al, al
adox r10, r12
adox r13, rbp
mov rbp, rdx
mov rdx, [ rcx + 0x0 ]
mulx rbx, r12, [ rsi + 0x0 ]
adcx r9, r14
adcx r8, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r14, [ rsp + 0x78 ]
mov rdx, [ rcx + 0x0 ]
mov [ rsp + 0xe8 ], r13
mov [ rsp + 0xf0 ], r10
mulx r10, r13, [ rsi + 0x8 ]
test al, al
adox r15, r14
adox rax, r11
adcx r15, r13
adcx r10, rax
mov rdx, rbp
mulx r11, rbp, [ rsi + 0x28 ]
mov r14, rbp
xor r13, r13
adox r14, [ rsp + 0xb8 ]
adox r11, [ rsp + 0xb0 ]
adcx r9, r12
adcx rbx, r8
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r8, [ rsp + 0x78 ]
mov rdx, rdi
mulx rbp, rdi, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], rbx
mov rbx, rdi
mov [ rsp + 0x100 ], r9
xor r9, r9
adox rbx, [ rsp + 0xd8 ]
adox rbp, [ rsp + 0xd0 ]
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, rdi, [ rsp + 0x78 ]
mov rdx, r12
mov [ rsp + 0x108 ], rax
mulx rax, r12, [ rsi + 0x20 ]
adcx r14, rdi
adcx r9, r11
xor r11, r11
adox rbx, r12
adox rax, rbp
adcx r15, [ rsp + 0x28 ]
adcx r10, [ rsp + 0x20 ]
mov rbp, rdx
mov rdx, [ rcx + 0x0 ]
mulx r12, rdi, [ rsi + 0x18 ]
add r14, rdi
adcx r12, r9
xor rdx, rdx
adox r14, [ rsp + 0x10 ]
adox r12, [ rsp + 0x8 ]
mov rdx, [ rcx + 0x0 ]
mulx r9, r11, [ rsi + 0x10 ]
adcx rbx, r8
adcx rax, [ rsp + 0x108 ]
mov rdx, [ rcx + 0x18 ]
mulx rdi, r8, [ rsi + 0x0 ]
add rbx, r11
adcx r9, rax
mov rdx, [ rcx + 0x10 ]
mulx rax, r11, [ rsi + 0x8 ]
test al, al
adox r14, r11
adox rax, r12
adcx r14, r8
adcx rdi, rax
mov rdx, [ rsp + 0xf8 ]
mov r12, [ rsp + 0x100 ]
shrd r12, rdx, 58
shr rdx, 58
xor r8, r8
adox r15, r12
adox rdx, r10
mov r10, rdx
mov rdx, [ rsi + 0x38 ]
mulx rax, r11, rbp
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, [ rcx + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x110 ], rax
mov [ rsp + 0x118 ], r11
mulx r11, rax, [ rsp + 0x78 ]
adcx rbx, r12
adcx r8, r9
mov rdx, [ rsi + 0x0 ]
mulx r12, r9, [ rcx + 0x10 ]
test al, al
adox rbx, r9
adox r12, r8
mov rdx, r15
shrd rdx, r10, 58
shr r10, 58
add rbx, rdx
adcx r10, r12
mov r8, 0x3ffffffffffffff 
and r15, r8
mov r9, rbx
shrd r9, r10, 58
shr r10, 58
add r14, r9
adcx r10, rdi
mov rdx, [ rsi + 0x40 ]
mulx r12, rdi, r13
xor rdx, rdx
adox rdi, [ rsp + 0x118 ]
adox r12, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x38 ]
mulx r9, r13, [ rsp + 0x78 ]
adcx rdi, rax
adcx r11, r12
and rbx, r8
mov rdx, rbp
mulx rax, rbp, [ rsi + 0x40 ]
adox rbp, r13
adox r9, rax
adcx rbp, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
mov rdx, [ rcx + 0x10 ]
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rcx + 0x8 ]
mulx r8, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r15
mulx r15, rbx, [ rcx + 0x0 ]
test al, al
adox rbp, rax
adox r8, r9
mov rdx, [ rcx + 0x8 ]
mulx rax, r9, [ rsi + 0x20 ]
adcx rdi, rbx
adcx r15, r11
mov rdx, r14
shrd rdx, r10, 58
shr r10, 58
mov r11, rdx
add r11, [ rsp + 0xf0 ]
adcx r10, [ rsp + 0xe8 ]
xor rbx, rbx
adox rdi, r9
adox rax, r15
adcx rbp, [ rsp - 0x20 ]
adcx r8, [ rsp - 0x28 ]
mov r9, 0x3a 
bzhi r15, r14, r9
mov rdx, [ rsi + 0x8 ]
mulx rbx, r14, [ rcx + 0x20 ]
adox rdi, r12
adox r13, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, r12, [ rcx + 0x18 ]
bzhi rdx, r11, r9
adox rdi, [ rsp + 0x60 ]
adox r13, [ rsp + 0x58 ]
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x20 ], rdx
add rbp, r12
adcx rax, r8
mov rdx, [ rcx + 0x10 ]
mulx r12, r8, [ rsi + 0x28 ]
xor rdx, rdx
adox rdi, r14
adox rbx, r13
mov [ r9 + 0x18 ], r15
mov rdx, [ rsi + 0x0 ]
mulx r14, r15, [ rcx + 0x28 ]
mov rdx, [ rcx + 0x8 ]
mulx r9, r13, [ rsi + 0x38 ]
adcx rdi, r15
adcx r14, rbx
test al, al
adox rbp, [ rsp + 0x98 ]
adox rax, [ rsp + 0x90 ]
mov rdx, [ rcx + 0x30 ]
mulx r15, rbx, [ rsi + 0x0 ]
mov rdx, r8
adcx rdx, [ rsp + 0xc8 ]
adcx r12, [ rsp + 0xc0 ]
shrd r11, r10, 58
shr r10, 58
add rdi, r11
adcx r10, r14
mov r8, rdi
shrd r8, r10, 58
shr r10, 58
mov r14, rdx
mov rdx, [ rcx + 0x28 ]
mov [ rsp + 0x130 ], r10
mulx r10, r11, [ rsi + 0x8 ]
test al, al
adox rbp, r11
adox r10, rax
adcx rbp, rbx
adcx r15, r10
mov rdx, [ rsi + 0x18 ]
mulx rbx, rax, [ rcx + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, r11, [ rcx + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], rbp
mulx rbp, r15, [ rcx + 0x18 ]
add r14, r15
adcx rbp, r12
add r14, rax
adcx rbx, rbp
mov rdx, r13
test al, al
adox rdx, [ rsp + 0xa8 ]
adox r9, [ rsp + 0xa0 ]
mov r13, rdx
mov rdx, [ rcx + 0x10 ]
mulx rax, r12, [ rsi + 0x30 ]
adcx r13, r12
adcx rax, r9
mov rdx, [ rcx + 0x18 ]
mulx rbp, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, r9, [ rcx + 0x30 ]
xor rdx, rdx
adox r13, r15
adox rbp, rax
adcx r14, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
add r14, r11
adcx r10, rbx
mov rdx, [ rsi + 0x20 ]
mulx rax, r11, [ rcx + 0x20 ]
xor rdx, rdx
adox r13, r11
adox rax, rbp
adcx r13, [ rsp - 0x40 ]
adcx rax, [ rsp - 0x48 ]
mov r15, r8
xor rbp, rbp
adox r15, [ rsp + 0x140 ]
mov rdx, [ rsp + 0x130 ]
adox rdx, [ rsp + 0x138 ]
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, [ rcx + 0x38 ]
adcx r14, rbx
adcx r11, r10
mov rdx, r15
shrd rdx, r8, 58
shr r8, 58
add r14, rdx
adcx r8, r11
mov r10, r14
shrd r10, r8, 58
shr r8, 58
mov rbx, 0x3a 
bzhi r11, r14, rbx
mov rdx, [ rcx + 0x38 ]
mulx rbp, r14, [ rsi + 0x8 ]
adox r13, r9
adox r12, rax
test al, al
adox r13, r14
adox rbp, r12
mov rdx, [ rcx + 0x40 ]
mulx rax, r9, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], r11
adcx r13, r9
adcx rax, rbp
add r13, r10
adcx r8, rax
mov r10, 0x1ffffffffffffff 
mov r11, r13
and r11, r10
bzhi r14, [ rsp + 0x100 ], rbx
shrd r13, r8, 57
shr r8, 57
bzhi r12, rdi, rbx
mov [ rdx + 0x28 ], r12
adox r13, r14
mov rdi, 0x0 
adox r8, rdi
mov [ rdx + 0x40 ], r11
mov rbp, r13
shrd rbp, r8, 58
add rbp, [ rsp + 0x128 ]
bzhi r9, rbp, rbx
shr rbp, 58
mov [ rdx + 0x8 ], r9
bzhi rax, r15, rbx
mov [ rdx + 0x30 ], rax
add rbp, [ rsp + 0x120 ]
bzhi r15, r13, rbx
mov [ rdx + 0x10 ], rbp
mov [ rdx + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 456
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.3832
; seed 1626744188929601 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10231235 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=52, initial num_batches=31): 207924 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020322473288904026
; number reverted permutation / tried permutation: 66345 / 89741 =73.929%
; number reverted decision / tried decision: 55701 / 90258 =61.713%
; validated in 4.335s
