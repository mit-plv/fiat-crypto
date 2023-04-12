SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rbp
mulx rbp, r15, [ rax + 0x10 ]
xor rdx, rdx
adox r9, r12
adox r15, rbx
mov rdx, [ rax + 0x10 ]
mulx r12, rbx, [ rsi + 0x18 ]
adcx r10, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r12
mulx r12, rdi, [ rax + 0x10 ]
adcx rdi, r11
adox rcx, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, r11, [ rax + 0x18 ]
mov rdx, 0x0 
adox r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], rdi
mulx rdi, rbx, [ rax + 0x0 ]
adcx r11, r12
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r11
mulx r11, r12, rbx
adc rbp, 0x0
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r10
mulx r10, rbp, [ rsi + 0x0 ]
test al, al
adox rbp, rdi
mov rdx, 0xffffffff 
mov [ rsp - 0x8 ], r8
mulx r8, rdi, rbx
adcx rdi, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x0 ], rcx
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r8, rdx
adox r11, r10
adox r13, rcx
adox r14, rdx
test al, al
adox r12, rbx
adox rdi, rbp
mov r12, 0xffffffff00000001 
mov rdx, rbx
mulx r10, rbx, r12
adcx rdi, [ rsp - 0x40 ]
adox r8, r11
adox rbx, r13
adcx r9, r8
mov rdx, 0xffffffffffffffff 
mulx rcx, rbp, rdi
adox r10, r14
adcx r15, rbx
adcx r10, [ rsp + 0x0 ]
mov r11, 0xffffffff 
mov rdx, rdi
mulx r13, rdi, r11
seto r14b
movzx r14, r14b
adcx r14, [ rsp - 0x8 ]
mov r8, -0x2 
inc r8
adox rdi, rcx
seto bl
inc r8
adox rbp, rdx
adox rdi, r9
movzx rbp, bl
lea rbp, [ rbp + r13 ]
mulx rcx, r9, r12
adox rbp, r15
adox r9, r10
setc dl
clc
adcx rdi, [ rsp - 0x48 ]
adox rcx, r14
movzx r15, dl
adox r15, r8
mov r10, 0xffffffffffffffff 
mov rdx, rdi
mulx r13, rdi, r10
mulx rbx, r14, r11
adcx rbp, [ rsp - 0x10 ]
mov r12, -0x3 
inc r12
adox r14, r13
adcx r9, [ rsp - 0x28 ]
adcx rcx, [ rsp - 0x20 ]
adox rbx, r8
mov r13, -0x3 
inc r13
adox rdi, rdx
adox r14, rbp
adox rbx, r9
mov rdi, 0xffffffff00000001 
mulx rbp, r13, rdi
adox r13, rcx
adcx r15, [ rsp - 0x18 ]
adox rbp, r15
seto dl
adc dl, 0x0
movzx rdx, dl
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r12, r8, [ rsi + 0x18 ]
adox r8, r15
adcx rcx, r14
adcx r8, rbx
mov rdx, rcx
mulx r14, rcx, r10
adox r12, [ rsp - 0x30 ]
adcx r12, r13
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mulx r15, r13, [ rsi + 0x18 ]
adox r13, [ rsp - 0x38 ]
mov rdx, 0x0 
adox r15, rdx
mov rdx, rbx
mulx rdi, rbx, r11
mov r11, -0x2 
inc r11
adox rbx, r14
seto r14b
inc r11
adox rcx, rdx
adox rbx, r8
movzx rcx, r14b
lea rcx, [ rcx + rdi ]
mov r8, 0xffffffff00000001 
mulx r14, rdi, r8
adcx r13, rbp
adox rcx, r12
movzx rbp, r9b
adcx rbp, r15
adox rdi, r13
adox r14, rbp
seto r9b
adc r9b, 0x0
movzx r9, r9b
mov rdx, rbx
sub rdx, r10
mov r12, rcx
mov r15, 0xffffffff 
sbb r12, r15
mov r13, rdi
sbb r13, 0x00000000
mov rbp, r14
sbb rbp, r8
movzx r8, r9b
sbb r8, 0x00000000
cmovc rbp, r14
cmovc rdx, rbx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], rdx
cmovc r12, rcx
mov [ r8 + 0x8 ], r12
cmovc r13, rdi
mov [ r8 + 0x10 ], r13
mov [ r8 + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6089
; seed 2329860144215730 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1252883 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=115, initial num_batches=31): 79628 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0635558148685871
; number reverted permutation / tried permutation: 65848 / 90090 =73.091%
; number reverted decision / tried decision: 55928 / 89909 =62.205%
; validated in 2.278s
