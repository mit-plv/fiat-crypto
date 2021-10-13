SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x30
imul rax, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
imul rdx, rax, 0x2; x2 <- x1 * 0x2
imul rcx, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
mulx r8, r9, [ rsi + 0x8 ]; x22, x21<- arg1[1] * x2
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
imul r15, rcx, 0x2; x5 <- x4 * 0x2
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mov r14, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mulx r15, r13, r15; x18, x17<- arg1[2] * x5
xor rdx, rdx
adox r13, r9
adox r8, r15
adcx r13, r11
adcx r10, r8
mov r11, 0x7ffffffffffff ; moving imm to reg
mov r9, r13; x48, copying x43 here, cause x43 is needed in a reg for other than x48, namely all: , x48, x47, size: 2
and r9, r11; x48 <- x43&0x7ffffffffffff
imul r15, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mov r8, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mulx r15, r12, r15; x36, x35<- arg1[0] * x8
shrd r13, r10, 51; x47 <- x45||x43 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r8, r14; x16, x15<- arg1[2] * x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mulx rcx, rbp, rcx; x14, x13<- arg1[3] * x4
xor rdx, rdx
adox rbp, r8
adox r10, rcx
adcx rbp, r12
adcx r15, r10
test al, al
adox rbp, r13
adox r15, rdx
imul r12, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov r13, rbp; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x85, x84, size: 2
shrd r13, r15, 51; x84 <- x83||x81 >> 51
mov r8, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r10, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
mov rdx, r12; x7 to rdx
mulx r15, r8, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
xchg rdx, r14; x2, swapping with x7, which is currently in rdx
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
mulx rdx, rbx, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x2
test al, al
adox rbx, r10
adox rcx, rdx
adcx rbx, r8
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r13
adcx r15, rcx
mov r13, 0x0 ; moving imm to reg
adox r15, r13
mov r8, rbx; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x90, x89, size: 2
shrd r8, r15, 51; x89 <- x88||x86 >> 51
imul rdx, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
mulx rcx, r15, [ rsi + 0x0 ]; x32, x31<- arg1[0] * x6
mov r13, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, r10, r14; x26, x25<- arg1[1] * x7
mov rdx, rax; x1 to rdx
mulx rdx, rax, [ rsi + 0x20 ]; x10, x9<- arg1[4] * x1
add rax, r10; could be done better, if r0 has been u8 as well
adcx r14, rdx
xor r10, r10
adox rax, r15
adox rcx, r14
adcx rax, r8
adc rcx, 0x0
imul r8, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov r15, rax; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd r15, rcx, 51; x94 <- x93||x91 >> 51
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r14, r8; x30, x29<- arg1[0] * x3
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, rcx, r13; x24, x23<- arg1[1] * x6
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r11, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
add r11, rcx; could be done better, if r0 has been u8 as well
adcx r13, r10
xor rdx, rdx
adox r11, r14
adcx r11, r15
adox r8, r13
adc r8, 0x0
mov r15, r11; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x99, x100, size: 2
shrd r15, r8, 51; x99 <- x98||x96 >> 51
imul r15, r15, 0x13; x101 <- x99 * 0x13
lea r9, [ r9 + r15 ]
mov r14, r9; x103, copying x102 here, cause x102 is needed in a reg for other than x103, namely all: , x103, x104, size: 2
shr r14, 51; x103 <- x102>> 51
mov rcx, 0x33 ; moving imm to reg
bzhi rbp, rbp, rcx; x85 <- x81 (only least 0x33 bits)
lea r14, [ r14 + rbp ]
bzhi rcx, r14, rcx; x107 <- x105 (only least 0x33 bits)
mov r10, 0x33 ; moving imm to reg
bzhi rbx, rbx, r10; x90 <- x86 (only least 0x33 bits)
shr r14, 51; x106 <- x105>> 51
mov r13, 0x7ffffffffffff ; moving imm to reg
and r11, r13; x100 <- x96&0x7ffffffffffff
mov [ rdi + 0x20 ], r11; out1[4] = x100
lea r14, [ r14 + rbx ]
and r9, r13; x104 <- x102&0x7ffffffffffff
mov [ rdi + 0x8 ], rcx; out1[1] = x107
and rax, r13; x95 <- x91&0x7ffffffffffff
mov [ rdi + 0x0 ], r9; out1[0] = x104
mov [ rdi + 0x10 ], r14; out1[2] = x108
mov [ rdi + 0x18 ], rax; out1[3] = x95
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.1908
; seed 34149503 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; time needed: 4042 ms / 500 evals=> 8.084ms/eval
; Time spent for assembling and measureing (initial batch_size=146, initial num_batches=31): 452 ms
; number of used evaluations: 500
; Ratio (time for assembling + measure)/(total runtime for 500 evals): 0.11182582879762494
; number reverted permutation/ tried permutation: 218 / 272 =80.147%
; number reverted decision/ tried decision: 170 / 228 =74.561%
