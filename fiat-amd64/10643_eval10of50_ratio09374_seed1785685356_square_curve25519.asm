SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x38
imul rax, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
imul r10, rax, 0x2; x2 <- x1 * 0x2
imul r11, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
imul rdx, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul rcx, rdx, 0x2; x5 <- x4 * 0x2
imul r8, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
imul r9, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
imul r15, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mov r14, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mulx r13, r12, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
mulx rbp, rbx, r10; x22, x21<- arg1[1] * x2
mov rdx, rcx; x5 to rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x5
test al, al
adox rcx, rbx
adcx rcx, r12
adox rbp, rdx
adcx r13, rbp
mov r12, rcx; x47, copying x43 here, cause x43 is needed in a reg for other than x47, namely all: , x47, x48, size: 2
shrd r12, r13, 51; x47 <- x45||x43 >> 51
mov rbx, 0x33 ; moving imm to reg
bzhi rcx, rcx, rbx; x48 <- x43 (only least 0x33 bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rbp, r15; x36, x35<- arg1[0] * x8
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rbx, r10; x16, x15<- arg1[2] * x2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
mulx r14, rdi, r14; x14, x13<- arg1[3] * x4
adox rdi, rbx
clc;
adcx rdi, rbp
setc dl; spill CF x78 to reg (rdx)
clc;
adcx rdi, r12
adox r13, r14
movzx rdx, dl
lea r15, [ r15 + r13 ]
lea r15, [ r15 + rdx ]
adc r15, 0x0
mov r12, rdi; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r12, r15, 51; x84 <- x83||x81 >> 51
mov rbp, 0x7ffffffffffff ; moving imm to reg
and rdi, rbp; x85 <- x81&0x7ffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbx, r14, r9; x34, x33<- arg1[0] * x7
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r15, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, rbp, r10; x12, x11<- arg1[3] * x2
adox rbp, r15
adcx rbp, r14
setc dl; spill CF x70 to reg (rdx)
clc;
adcx rbp, r12
adox r13, r10
movzx rdx, dl
lea rbx, [ rbx + r13 ]
lea rbx, [ rbx + rdx ]
adc rbx, 0x0
mov r12, rbp; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x89, x90, size: 2
shrd r12, rbx, 51; x89 <- x88||x86 >> 51
mov r14, 0x7ffffffffffff ; moving imm to reg
and rbp, r14; x90 <- x86&0x7ffffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, r10, r8; x32, x31<- arg1[0] * x6
mov rdx, r9; x7 to rdx
mulx rdx, r9, [ rsi + 0x8 ]; x26, x25<- arg1[1] * x7
xchg rdx, rax; x1, swapping with x26, which is currently in rdx
mulx rdx, r13, [ rsi + 0x20 ]; x10, x9<- arg1[4] * x1
adox r13, r9
adcx r13, r10
seto bl; spill OF x58 to reg (rbx)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r12
movzx rbx, bl
lea rax, [ rax + rdx ]
lea rax, [ rax + rbx ]
adcx r15, rax
mov r12, 0x0 ; moving imm to reg
adox r15, r12
mov r9, r13; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd r9, r15, 51; x94 <- x93||x91 >> 51
mov rdx, 0x33 ; moving imm to reg
bzhi r13, r13, rdx; x95 <- x91 (only least 0x33 bits)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, r11; x30, x29<- arg1[0] * x3
mov rdx, r8; x6 to rdx
mulx rdx, r8, [ rsi + 0x8 ]; x24, x23<- arg1[1] * x6
mov rax, rdx; preserving value of x24 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, r12, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
adox r12, r8
clc;
adcx r12, rbx
seto dl; spill OF x50 to reg (rdx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r9
movzx rdx, dl
lea rax, [ rax + r15 ]
lea rax, [ rax + rdx ]
adcx r11, rax
adox r11, r10
mov r9, r12; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x99, x100, size: 2
shrd r9, r11, 51; x99 <- x98||x96 >> 51
mov rbx, 0x33 ; moving imm to reg
bzhi r12, r12, rbx; x100 <- x96 (only least 0x33 bits)
imul r9, r9, 0x13; x101 <- x99 * 0x13
lea rcx, [ rcx + r9 ]
mov r8, rcx; x103, copying x102 here, cause x102 is needed in a reg for other than x103, namely all: , x103, x104, size: 2
shr r8, 51; x103 <- x102>> 51
bzhi rcx, rcx, rbx; x104 <- x102 (only least 0x33 bits)
lea r8, [ r8 + rdi ]
mov rdi, r8; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, x107, size: 2
shr rdi, 51; x106 <- x105>> 51
bzhi r8, r8, rbx; x107 <- x105 (only least 0x33 bits)
lea rdi, [ rdi + rbp ]
mov rbp, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ rbp + 0x0 ], rcx; out1[0] = x104
mov [ rbp + 0x8 ], r8; out1[1] = x107
mov [ rbp + 0x10 ], rdi; out1[2] = x108
mov [ rbp + 0x18 ], r13; out1[3] = x95
mov [ rbp + 0x20 ], r12; out1[4] = x100
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x38 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.9374
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 248 ms / 10 evals=> 24.8ms/eval
; Time spent for assembling and measureing (initial batch_size=160, initial num_batches=31): 33 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.13306451612903225
; number reverted permutation/ tried permutation: 2 / 2 =100.000%
; number reverted decision/ tried decision: 5 / 8 =62.500%