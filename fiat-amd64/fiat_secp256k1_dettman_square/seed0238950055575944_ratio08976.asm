SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x8 ]
mov rdx, r11
shl rdx, 0x1
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rdx
mov rdx, 0x34 
bzhi r9, rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r11
mov rdx, 0x1 
mov [ rsp - 0x60 ], r14
shlx r14, [ rsi + 0x0 ], rdx
mov rdx, r11
mov [ rsp - 0x58 ], r15
mulx r15, r11, [ rsi + 0x18 ]
mov rdx, r14
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
shrd rax, r10, 52
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rax
mov [ rsp - 0x30 ], r9
mulx r9, rax, rdx
xor rdx, rdx
adox r13, r14
adox rdi, r12
adcx rcx, r11
adcx r15, r8
mov r8, [ rsi + 0x18 ]
lea r11, [r8 + r8]
mov rdx, r10
mulx r8, r10, [ rsi + 0x20 ]
xchg rdx, r11
mulx r12, r14, [ rsi + 0x20 ]
add rcx, r10
adcx r8, r15
mov rdx, r11
mulx r15, r11, [ rsi + 0x18 ]
test al, al
adox rbx, r11
adox r15, rbp
mov rbp, [ rsi + 0x10 ]
lea r10, [rbp + rbp]
mov rbp, 0x1000003d10 
xchg rdx, rbp
mov [ rsp - 0x28 ], rdi
mulx rdi, r11, [ rsp - 0x30 ]
adcx r11, rbx
adcx r15, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbx, r10
mov rdx, r11
shrd rdx, r15, 52
mov r15, 0x1000003d10 
xchg rdx, r15
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r12
mulx r12, r13, [ rsp - 0x38 ]
xor rdx, rdx
adox r15, rcx
adox r8, rdx
adcx r13, r15
adcx r8, r12
mov rcx, 0x34 
bzhi r12, r11, rcx
adox rbx, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
mov rdx, r10
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, r13
shrd rdx, r8, 52
add rdx, rbx
adc rdi, 0x0
test al, al
adox rax, r10
adox r11, r9
bzhi r9, r13, rcx
mov r15, r9
shr r15, 48
bzhi r13, rdx, rcx
shl r13, 4
shrd rdx, rdi, 52
mov r8, 0xffffffffffff 
and r9, r8
lea r13, [ r13 + r15 ]
xchg rdx, rbp
mulx r10, rbx, [ rsi + 0x8 ]
adox rbp, rax
mov rdx, 0x0 
adox r11, rdx
mov rdi, 0x1000003d1 
mov rdx, rdi
mulx rax, rdi, r13
bzhi r15, rbp, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r13, rdx
mov rdx, 0x1000003d10 
mov [ rsp - 0x10 ], r9
mulx r9, r8, r15
adox rdi, r13
adox rcx, rax
shrd rbp, r11, 52
mov r11, rdi
shrd r11, rcx, 52
xor rax, rax
adox r11, rbx
adox r10, rax
adcx r8, r11
adcx r10, r9
add rbp, r14
mov rbx, [ rsp - 0x18 ]
adc rbx, 0x0
mov r14, 0xfffffffffffff 
mov r15, rbp
and r15, r14
mov r13, r8
shrd r13, r10, 52
xor r9, r9
adox r13, [ rsp - 0x20 ]
mov rax, [ rsp - 0x28 ]
adox rax, r9
and rdi, r14
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], rdi
shrd rbp, rbx, 52
mulx r10, r11, r15
mulx r15, rbx, rbp
and r8, r14
adox r11, r13
adox rax, r10
mov r13, r11
shrd r13, rax, 52
mov [ rcx + 0x8 ], r8
lea r12, [ r12 + r13 ]
xor rdi, rdi
adox rbx, r12
adox r15, rdi
mov r9, rbx
shrd r9, r15, 52
and r11, r14
mov [ rcx + 0x10 ], r11
add r9, [ rsp - 0x10 ]
mov [ rcx + 0x20 ], r9
and rbx, r14
mov [ rcx + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.8976
; seed 0238950055575944 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9274 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=161, initial num_batches=31): 648 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.0698727625620013
; number reverted permutation / tried permutation: 422 / 468 =90.171%
; number reverted decision / tried decision: 322 / 531 =60.640%
; validated in 0.354s
