SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0x48 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x18 ], rbx; saving to stack
mov [ rsp + 0x20 ], rbp; saving to stack
mov [ rsp + 0x28 ], r12; saving to stack
mov [ rsp + 0x30 ], r13; saving to stack
mov [ rsp + 0x38 ], r14; saving to stack
mov [ rsp + 0x40 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r11, rax; x8, x7<- x4 * arg1[2]
mov rdx, rax; x4 to rdx
mulx rax, rbx, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
mulx rbp, r12, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mulx r14, r15, r12; x25, x24<- x11 * 0xffffffffffffffff
add rbx, rbp; could be done better, if r0 has been u8 as well
adcx r11, rax
xchg rdx, r13; x4, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, rcx, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
adcx rcx, r10
mov r8, [ rsi + 0x8 ]; load m64 x1 to register64
adc rdx, 0x0
xor r9, r9
adox r15, r12
xchg rdx, r8; x1, swapping with x19, which is currently in rdx
mulx r15, r10, [ rsi + 0x0 ]; x46, x45<- x1 * arg1[0]
mov rax, 0xffffffff ; moving imm to reg
xchg rdx, r12; x11, swapping with x1, which is currently in rdx
mulx rbp, r9, rax; x23, x22<- x11 * 0xffffffff
adcx r9, r14
mov r14, 0x0 ; moving imm to reg
adcx rbp, r14
adox r9, rbx
clc;
adcx r10, r9
mov rbx, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r9, r14, r12; x44, x43<- x1 * arg1[1]
adox rbp, r11
mov rdx, r10; x54 to rdx
mulx r10, r11, r13; x69, x68<- x54 * 0xffffffffffffffff
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r13, rdi, rax; x67, x66<- x54 * 0xffffffff
seto al; spill OF x34 to reg (rax)
mov [ rsp + 0x8 ], r9; spilling x44 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r15
adcx r14, rbp
seto r15b; spill OF x48 to reg (r15)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rdx
mov r11, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r11; 0xffffffff00000001, swapping with x54, which is currently in rdx
mulx rbx, rbp, rbx; x21, x20<- x11 * 0xffffffff00000001
setc dl; spill CF x57 to reg (rdx)
clc;
adcx rdi, r10
adcx r13, r9
adox rdi, r14
clc;
mov r10, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r10; loading flag
adcx rcx, rbp
xchg rdx, r12; x1, swapping with x57, which is currently in rdx
mulx rax, r14, [ rsi + 0x10 ]; x42, x41<- x1 * arg1[2]
adcx rbx, r8
mulx rdx, r8, [ rsi + 0x18 ]; x40, x39<- x1 * arg1[3]
setc bpl; spill CF x38 to reg (rbp)
clc;
movzx r15, r15b
adcx r15, r10; loading flag
adcx r14, [ rsp + 0x8 ]
mov r15, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r11; x54, swapping with x40, which is currently in rdx
mulx rdx, r9, r15; x65, x64<- x54 * 0xffffffff00000001
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r8, rax
mov rax, 0x0 ; moving imm to reg
adcx r11, rax
clc;
mov rax, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rax; loading flag
adcx rcx, r14
adox r13, rcx
adcx r8, rbx
adox r9, r8
movzx r12, bpl; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adcx r12, r11
adox rdx, r12
mov rbp, rdx; preserving value of x81 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r14, r10; x91, x90<- x2 * arg1[0]
mov rdx, r10; x2 to rdx
mulx r10, r11, [ rsi + 0x8 ]; x89, x88<- x2 * arg1[1]
seto cl; spill OF x82 to reg (rcx)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, rdi
movzx rdi, cl; x83, copying x82 here, cause x82 is needed in a reg for other than x83, namely all: , x83, size: 1
adcx rdi, rax
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx r12, rcx, r14; x114, x113<- x99 * 0xffffffffffffffff
xchg rdx, r8; x2, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rax, r15, [ rsi + 0x10 ]; x87, x86<- x2 * arg1[2]
clc;
adcx r11, rbx
mov rbx, 0xffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffff, swapping with x2, which is currently in rdx
mov [ rsp + 0x10 ], rdi; spilling x83 to mem
mulx r8, rdi, r14; x112, x111<- x99 * 0xffffffff
adox r11, r13
setc r13b; spill CF x93 to reg (r13)
clc;
adcx rdi, r12
setc r12b; spill CF x116 to reg (r12)
clc;
adcx rcx, r14
mov rcx, [ rsi + 0x18 ]; load m64 x3 to register64
adcx rdi, r11
setc r11b; spill CF x121 to reg (r11)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r10, r15
adox r10, r9
mov rdx, rbx; x2 to rdx
mulx rdx, rbx, [ rsi + 0x18 ]; x85, x84<- x2 * arg1[3]
adcx rbx, rax
adox rbx, rbp
mov r9, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r14; x99, swapping with x85, which is currently in rdx
mulx rdx, rbp, r9; x110, x109<- x99 * 0xffffffff00000001
mov rax, 0x0 ; moving imm to reg
adcx r14, rax
movzx r15, r12b; x117, copying x116 here, cause x116 is needed in a reg for other than x117, namely all: , x117, size: 1
lea r15, [ r15 + r8 ]
xchg rdx, rcx; x3, swapping with x110, which is currently in rdx
mulx r13, r8, [ rsi + 0x0 ]; x136, x135<- x3 * arg1[0]
clc;
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r12; loading flag
adcx r10, r15
mov r11, [ rsp + 0x10 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adox r11, r14
adcx rbp, rbx
adcx rcx, r11
seto bl; spill OF x108 to reg (rbx)
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, rdi
movzx rdi, bl; x128, copying x108 here, cause x108 is needed in a reg for other than x128, namely all: , x128, size: 1
adcx rdi, rax
mulx r15, rbx, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
mov r11, 0xffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffff, swapping with x3, which is currently in rdx
mulx rax, r14, r8; x157, x156<- x144 * 0xffffffff
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with 0xffffffff, which is currently in rdx
mulx r12, r9, r8; x159, x158<- x144 * 0xffffffffffffffff
clc;
adcx r9, r8
setc r9b; spill CF x164 to reg (r9)
clc;
adcx r14, r12
setc r12b; spill CF x161 to reg (r12)
clc;
adcx rbx, r13
adox rbx, r10
xchg rdx, r11; x3, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r13, r10, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
adcx r10, r15
adox r10, rbp
setc bpl; spill CF x140 to reg (rbp)
clc;
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r15; loading flag
adcx rbx, r14
movzx r9, r12b; x162, copying x161 here, cause x161 is needed in a reg for other than x162, namely all: , x162, size: 1
lea r9, [ r9 + rax ]
adcx r9, r10
setc al; spill CF x168 to reg (rax)
seto r14b; spill OF x149 to reg (r14)
mov r12, rbx; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
sub r12, r11
mulx rdx, r10, [ rsi + 0x18 ]; x130, x129<- x3 * arg1[3]
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r15; loading flag
adox r13, r10
mov rbp, 0x0 ; moving imm to reg
adox rdx, rbp
mov r10, r9; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov rbp, 0xffffffff ; moving imm to reg
sbb r10, rbp
mov r15, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r15; 0xffffffff00000001, swapping with x143, which is currently in rdx
mulx r8, rbp, r8; x155, x154<- x144 * 0xffffffff00000001
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r11; loading flag
adox rcx, r13
adox r15, rdi
seto dil; spill OF x153 to reg (rdi)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r14; loading flag
adox rcx, rbp
adox r8, r15
movzx rax, dil; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
adox rax, r11
mov r13, rcx; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r13, 0x00000000
mov rbp, r8; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
sbb rbp, rdx
sbb rax, 0x00000000
cmovc r13, rcx; if CF, x186<- x169 (nzVar)
cmovc r10, r9; if CF, x185<- x167 (nzVar)
cmovc rbp, r8; if CF, x187<- x171 (nzVar)
mov rax, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rax + 0x18 ], rbp; out1[3] = x187
cmovc r12, rbx; if CF, x184<- x165 (nzVar)
mov [ rax + 0x10 ], r13; out1[2] = x186
mov [ rax + 0x0 ], r12; out1[0] = x184
mov [ rax + 0x8 ], r10; out1[1] = x185
mov rbx, [ rsp + 0x18 ]; restoring from stack
mov rbp, [ rsp + 0x20 ]; restoring from stack
mov r12, [ rsp + 0x28 ]; restoring from stack
mov r13, [ rsp + 0x30 ]; restoring from stack
mov r14, [ rsp + 0x38 ]; restoring from stack
mov r15, [ rsp + 0x40 ]; restoring from stack
add rsp, 0x48 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 80.24, best 57.774436090225564, lastGood 61.46153846153846
; seed 851790244847742 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 695542 ms / 60000 runs=> 11.592366666666667ms/run
; Time spent for assembling and measureing (initial batch_size=129, initial num_batches=101): 201079 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2890968482133358
; number reverted permutation/ tried permutation: 27136 / 30008 =90.429%
; number reverted decision/ tried decision: 22207 / 29993 =74.041%