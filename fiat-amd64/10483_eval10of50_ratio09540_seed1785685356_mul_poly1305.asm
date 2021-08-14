SECTION .text
	GLOBAL mul_poly1305
mul_poly1305:
sub rsp, 0x28
imul rax, [ rdx + 0x10 ], 0x5; x10000 <- arg2[2] * 0x5
imul r10, [ rdx + 0x10 ], 0xa; x10002 <- arg2[2] * 0xa
imul r11, [ rdx + 0x8 ], 0xa; x10001 <- arg2[1] * 0xa
imul rcx, [ rdx + 0x8 ], 0x2; x10003 <- arg2[1] * 0x2
mov r8, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
mulx r9, r15, [ rsi + 0x0 ]; x18, x17<- arg1[0] * arg2[0]
mov rdx, r10; x10002 to rdx
mulx rdx, r10, [ rsi + 0x8 ]; x6, x5<- arg1[1] * x10002
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mov r14, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mulx r11, r13, r11; x4, x3<- arg1[2] * x10001
add r13, r10; could be done better, if r0 has been u8 as well
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r15
adcx r14, r11
adox r9, r14
mov r15, r13; x27, copying x23 here, cause x23 is needed in a reg for other than x27, namely all: , x27, x28, size: 2
shrd r15, r9, 44; x27 <- x25||x23 >> 44
mov r11, 0x2c ; moving imm to reg
bzhi r13, r13, r11; x28 <- x23 (only least 0x2c bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, r9, [ r8 + 0x8 ]; x16, x15<- arg1[0] * arg2[1]
mov rdx, [ r8 + 0x0 ]; arg2[0] to rdx
mulx r11, r10, [ rsi + 0x8 ]; x12, x11<- arg1[1] * arg2[0]
mov rdx, rax; x10000 to rdx
mulx rdx, rax, [ rsi + 0x10 ]; x2, x1<- arg1[2] * x10000
adox rax, r10
clc;
adcx rax, r9
seto r9b; spill OF x38 to reg (r9)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r15
movzx r9, r9b
lea r11, [ r11 + rdx ]
lea r11, [ r11 + r9 ]
adcx r14, r11
mov r15, 0x0 ; moving imm to reg
adox r14, r15
mov rdx, rax; x48, copying x45 here, cause x45 is needed in a reg for other than x48, namely all: , x48, x49, size: 2
shrd rdx, r14, 43; x48 <- x47||x45 >> 43
mov r9, 0x7ffffffffff ; moving imm to reg
and rax, r9; x49 <- x45&0x7ffffffffff
mov r11, rdx; preserving value of x48 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r15, [ r8 + 0x10 ]; x14, x13<- arg1[0] * arg2[2]
mov rdx, rcx; x10003 to rdx
mulx rdx, rcx, [ rsi + 0x8 ]; x10, x9<- arg1[1] * x10003
mov r10, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mulx r12, rbp, [ r8 + 0x0 ]; x8, x7<- arg1[2] * arg2[0]
adox rbp, rcx
adcx rbp, r15
adox r10, r12
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r11
adcx r14, r10
mov r11, 0x0 ; moving imm to reg
adox r14, r11
mov rcx, rbp; x53, copying x50 here, cause x50 is needed in a reg for other than x53, namely all: , x53, x54, size: 2
shrd rcx, r14, 43; x53 <- x52||x50 >> 43
and rbp, r9; x54 <- x50&0x7ffffffffff
imul rcx, rcx, 0x5; x55 <- x53 * 0x5
lea r13, [ r13 + rcx ]
mov r12, r13; x57, copying x56 here, cause x56 is needed in a reg for other than x57, namely all: , x57, x58, size: 2
shr r12, 44; x57 <- x56>> 44
mov r10, 0x2c ; moving imm to reg
bzhi r13, r13, r10; x58 <- x56 (only least 0x2c bits)
lea r12, [ r12 + rax ]
mov rax, r12; x60, copying x59 here, cause x59 is needed in a reg for other than x60, namely all: , x60, x61, size: 2
shr rax, 43; x60 <- x59>> 43
mov r14, 0x2b ; moving imm to reg
bzhi r12, r12, r14; x61 <- x59 (only least 0x2b bits)
lea rax, [ rax + rbp ]
mov [ rdi + 0x0 ], r13; out1[0] = x58
mov [ rdi + 0x8 ], r12; out1[1] = x61
mov [ rdi + 0x10 ], rax; out1[2] = x62
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
add rsp, 0x28 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.9540
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 381 ms / 10 evals=> 38.1ms/eval
; Time spent for assembling and measureing (initial batch_size=283, initial num_batches=31): 43 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.11286089238845144
; number reverted permutation/ tried permutation: 2 / 5 =40.000%
; number reverted decision/ tried decision: 4 / 5 =80.000%