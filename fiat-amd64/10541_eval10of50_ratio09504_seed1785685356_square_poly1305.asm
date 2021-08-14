SECTION .text
	GLOBAL square_poly1305
square_poly1305:
sub rsp, 0x10
imul rax, [ rsi + 0x10 ], 0x5; x1 <- arg1[2] * 0x5
imul r10, rax, 0x2; x2 <- x1 * 0x2
imul r11, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
imul rdx, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
imul r10, r10, 0x2; x10000 <- x2 * 0x2
imul rcx, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mov r8, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
mulx r9, r15, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg1[0]
mov rdx, r10; x10000 to rdx
mulx rdx, r10, [ rsi + 0x8 ]; x8, x7<- arg1[1] * x10000
test al, al
adox r10, r15
adox r9, rdx
mov r15, r10; x21, copying x17 here, cause x17 is needed in a reg for other than x21, namely all: , x21, x22, size: 2
shrd r15, r9, 44; x21 <- x19||x17 >> 44
mov rdx, 0xfffffffffff ; moving imm to reg
and r10, rdx; x22 <- x17&0xfffffffffff
xchg rdx, rcx; x4, swapping with 0xfffffffffff, which is currently in rdx
mulx rdx, r9, [ rsi + 0x0 ]; x14, x13<- arg1[0] * x4
xchg rdx, rax; x1, swapping with x14, which is currently in rdx
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mulx rdx, r14, [ rsi + 0x10 ]; x6, x5<- arg1[2] * x1
adox r14, r9
adcx r14, r15
adox rax, rdx
adc rax, 0x0
mov r15, r14; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x34, x35, size: 2
shrd r15, rax, 43; x34 <- x33||x31 >> 43
mov r9, 0x2b ; moving imm to reg
bzhi r14, r14, r9; x35 <- x31 (only least 0x2b bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rax, r8; x12, x11<- arg1[0] * x3
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, r9, r11; x10, x9<- arg1[1] * x10001
adox r9, rax
clc;
adcx r9, r15
adox r8, r11
adc r8, 0x0
mov rdx, r9; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x39, x40, size: 2
shrd rdx, r8, 43; x39 <- x38||x36 >> 43
mov r15, 0x2b ; moving imm to reg
bzhi r9, r9, r15; x40 <- x36 (only least 0x2b bits)
imul rdx, rdx, 0x5; x41 <- x39 * 0x5
lea r10, [ r10 + rdx ]
mov rax, r10; x43, copying x42 here, cause x42 is needed in a reg for other than x43, namely all: , x43, x44, size: 2
shr rax, 44; x43 <- x42>> 44
lea rax, [ rax + r14 ]
and r10, rcx; x44 <- x42&0xfffffffffff
mov r14, rax; x46, copying x45 here, cause x45 is needed in a reg for other than x46, namely all: , x46, x47, size: 2
shr r14, 43; x46 <- x45>> 43
bzhi rax, rax, r15; x47 <- x45 (only least 0x2b bits)
lea r14, [ r14 + r9 ]
mov [ rdi + 0x0 ], r10; out1[0] = x44
mov [ rdi + 0x8 ], rax; out1[1] = x47
mov [ rdi + 0x10 ], r14; out1[2] = x48
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
add rsp, 0x10 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.9504
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 312 ms / 10 evals=> 31.2ms/eval
; Time spent for assembling and measureing (initial batch_size=374, initial num_batches=31): 49 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.15705128205128205
; number reverted permutation/ tried permutation: 7 / 9 =77.778%
; number reverted decision/ tried decision: 1 / 1 =100.000%