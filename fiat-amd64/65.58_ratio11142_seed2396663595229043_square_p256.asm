SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0x98 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x68 ], rbx; saving to stack
mov [ rsp + 0x70 ], rbp; saving to stack
mov [ rsp + 0x78 ], r12; saving to stack
mov [ rsp + 0x80 ], r13; saving to stack
mov [ rsp + 0x88 ], r14; saving to stack
mov [ rsp + 0x90 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, rax; x4 to rdx
mulx rax, r11, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
mulx rbx, rbp, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
xor r12, r12
adox r11, rbx
mov r13, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r15, r10; x46, x45<- x1 * arg1[0]
mov rdx, 0xffffffff ; moving imm to reg
mulx rcx, r8, rbp; x23, x22<- x11 * 0xffffffff
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffffffffffff, swapping with 0xffffffff, which is currently in rdx
mulx rbx, r12, rbp; x25, x24<- x11 * 0xffffffffffffffff
adcx r8, rbx
setc bl; spill CF x27 to reg (rbx)
clc;
adcx r12, rbp
adcx r8, r11
setc r12b; spill CF x32 to reg (r12)
clc;
adcx r15, r8
mulx r11, r8, r15; x69, x68<- x54 * 0xffffffffffffffff
mov r9, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r11; spilling x69 to mem
mulx rdi, r11, r13; x8, x7<- x4 * arg1[2]
adox r11, rax
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, r9, r10; x44, x43<- x1 * arg1[1]
movzx rdx, bl; x28, copying x27 here, cause x27 is needed in a reg for other than x28, namely all: , x28, size: 1
lea rdx, [ rdx + rcx ]
seto cl; spill OF x16 to reg (rcx)
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rbx; loading flag
adox r11, rdx
seto r12b; spill OF x34 to reg (r12)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, r14
mov r14, 0xffffffff ; moving imm to reg
mov rdx, r14; 0xffffffff to rdx
mulx r14, rbx, r15; x67, x66<- x54 * 0xffffffff
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r9, r11
setc r11b; spill CF x57 to reg (r11)
clc;
adcx r8, r15
mov byte [ rsp + 0x10 ], r11b; spilling byte x57 to mem
mulx r8, r11, [ rsi + 0x0 ]; x91, x90<- x2 * arg1[0]
mov [ rsp + 0x18 ], r8; spilling x91 to mem
seto r8b; spill OF x48 to reg (r8)
mov [ rsp + 0x20 ], rax; spilling x44 to mem
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x8 ]
adcx rbx, r9
setc r9b; spill CF x76 to reg (r9)
clc;
adcx r11, rbx
mov rbx, 0x0 ; moving imm to reg
adox r14, rbx
mov rbx, rdx; preserving value of x2 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r13, rax, r13; x6, x5<- x4 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x28 ], r14; spilling x72 to mem
mov byte [ rsp + 0x30 ], r9b; spilling byte x76 to mem
mulx r14, r9, r11; x114, x113<- x99 * 0xffffffffffffffff
mov rdx, 0xffffffff00000001 ; moving imm to reg
mov [ rsp + 0x38 ], r14; spilling x114 to mem
mulx rbp, r14, rbp; x21, x20<- x11 * 0xffffffff00000001
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, rdx; loading flag
adox rdi, rax
setc cl; spill CF x100 to reg (rcx)
clc;
adcx r9, r11
setc r9b; spill CF x119 to reg (r9)
clc;
movzx r12, r12b
adcx r12, rdx; loading flag
adcx rdi, r14
mov rdx, r10; x1 to rdx
mulx r10, r12, [ rsi + 0x10 ]; x42, x41<- x1 * arg1[2]
mulx rdx, rax, [ rsi + 0x18 ]; x40, x39<- x1 * arg1[3]
setc r14b; spill CF x36 to reg (r14)
clc;
mov [ rsp + 0x40 ], rdx; spilling x40 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r12, [ rsp + 0x20 ]
adcx rax, r10
setc r8b; spill CF x52 to reg (r8)
movzx r10, byte [ rsp + 0x10 ]; load byte memx57 to register64
clc;
adcx r10, rdx; loading flag
adcx rdi, r12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r12, rbx; x89, x88<- x2 * arg1[1]
mov rdx, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x48 ], r8b; spilling byte x52 to mem
mov [ rsp + 0x50 ], r10; spilling x89 to mem
mulx r8, r10, r11; x112, x111<- x99 * 0xffffffff
mov rdx, 0x0 ; moving imm to reg
adox r13, rdx
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r14, r14b
adox r14, rdx; loading flag
adox r13, rbp
seto bpl; spill OF x38 to reg (rbp)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp + 0x18 ]
adcx rax, r13
seto r14b; spill OF x93 to reg (r14)
movzx r13, byte [ rsp + 0x30 ]; load byte memx76 to register64
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r13, rdx; loading flag
adox rdi, [ rsp + 0x28 ]
setc r13b; spill CF x61 to reg (r13)
clc;
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx rdi, r12
setc cl; spill CF x102 to reg (rcx)
clc;
adcx r10, [ rsp + 0x38 ]
mov rdx, rbx; x2 to rdx
mulx rbx, r12, [ rsi + 0x10 ]; x87, x86<- x2 * arg1[2]
mov byte [ rsp + 0x58 ], cl; spilling byte x102 to mem
mov rcx, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r15; x54, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x60 ], bpl; spilling byte x38 to mem
mulx rdx, rbp, rcx; x65, x64<- x54 * 0xffffffff00000001
mov rcx, 0x0 ; moving imm to reg
adcx r8, rcx
adox rbp, rax
clc;
mov rax, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rax; loading flag
adcx rdi, r10
setc r9b; spill CF x121 to reg (r9)
clc;
movzx r14, r14b
adcx r14, rax; loading flag
adcx r12, [ rsp + 0x50 ]
mov r14, rdx; preserving value of x65 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r15, r10, r15; x85, x84<- x2 * arg1[3]
adcx r10, rbx
adcx r15, rcx
movzx rdx, byte [ rsp + 0x48 ]; x53, copying x52 here, cause x52 is needed in a reg for other than x53, namely all: , x53, size: 1
mov rbx, [ rsp + 0x40 ]; load m64 x40 to register64
lea rdx, [ rdx + rbx ]; r8/64 + m8
clc;
movzx rbx, byte [ rsp + 0x60 ]; load byte memx38 to register64
movzx r13, r13b
adcx r13, rax; loading flag
adcx rdx, rbx
mov rbx, [ rsi + 0x18 ]; load m64 x3 to register64
adox r14, rdx
setc r13b; spill CF x63 to reg (r13)
movzx rdx, byte [ rsp + 0x58 ]; load byte memx102 to register64
clc;
adcx rdx, rax; loading flag
adcx rbp, r12
adcx r10, r14
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx r11, r12, r11; x110, x109<- x99 * 0xffffffff00000001
movzx r14, r13b; x83, copying x63 here, cause x63 is needed in a reg for other than x83, namely all: , x83, size: 1
adox r14, rcx
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r9, r9b
adox r9, rcx; loading flag
adox rbp, r8
adox r12, r10
xchg rdx, rbx; x3, swapping with 0xffffffff00000001, which is currently in rdx
mulx rax, r8, [ rsi + 0x18 ]; x130, x129<- x3 * arg1[3]
mulx r9, r13, [ rsi + 0x0 ]; x136, x135<- x3 * arg1[0]
mulx r10, rcx, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
adcx r15, r14
adox r11, r15
seto r14b; spill OF x128 to reg (r14)
adc r14b, 0x0
movzx r14, r14b
mulx rdx, r15, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
adox r13, rdi
adcx r15, r9
adcx rcx, rdx
adcx r8, r10
adox r15, rbp
mov rdi, 0xffffffff ; moving imm to reg
mov rdx, r13; x144 to rdx
mulx r13, rbp, rdi; x157, x156<- x144 * 0xffffffff
mov r9, 0xffffffffffffffff ; moving imm to reg
mulx r10, rdi, r9; x159, x158<- x144 * 0xffffffffffffffff
mov r9, 0x0 ; moving imm to reg
adcx rax, r9
clc;
adcx rbp, r10
adox rcx, r12
adcx r13, r9
clc;
adcx rdi, rdx
adcx rbp, r15
adcx r13, rcx
mulx rdx, r12, rbx; x155, x154<- x144 * 0xffffffff00000001
adox r8, r11
adcx r12, r8
movzx r11, r14b; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox r11, rax
adcx rdx, r11
setc r14b; spill CF x172 to reg (r14)
seto r15b; spill OF x153 to reg (r15)
mov r10, rbp; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
mov rax, 0xffffffffffffffff ; moving imm to reg
sub r10, rax
mov rcx, r13; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov r8, 0xffffffff ; moving imm to reg
sbb rcx, r8
movzx r11, r14b; x173, copying x172 here, cause x172 is needed in a reg for other than x173, namely all: , x173, size: 1
movzx r15, r15b
lea r11, [ r11 + r15 ]
mov r15, r12; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178--x179, x186, size: 2
sbb r15, 0x00000000
mov r14, rdx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
sbb r14, rbx
sbb r11, 0x00000000
cmovc r14, rdx; if CF, x187<- x171 (nzVar)
cmovc r10, rbp; if CF, x184<- x165 (nzVar)
cmovc rcx, r13; if CF, x185<- x167 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x0 ], r10; out1[0] = x184
mov [ r11 + 0x18 ], r14; out1[3] = x187
cmovc r15, r12; if CF, x186<- x169 (nzVar)
mov [ r11 + 0x8 ], rcx; out1[1] = x185
mov [ r11 + 0x10 ], r15; out1[2] = x186
mov rbx, [ rsp + 0x68 ]; restoring from stack
mov rbp, [ rsp + 0x70 ]; restoring from stack
mov r12, [ rsp + 0x78 ]; restoring from stack
mov r13, [ rsp + 0x80 ]; restoring from stack
mov r14, [ rsp + 0x88 ]; restoring from stack
mov r15, [ rsp + 0x90 ]; restoring from stack
add rsp, 0x98 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 87.165, best 63.865671641791046, lastGood 65.58208955223881
; seed 2396663595229043 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1054290 ms / 60000 runs=> 17.5715ms/run
; Time spent for assembling and measureing (initial batch_size=134, initial num_batches=101): 262928 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.24938868812186402
; number reverted permutation/ tried permutation: 23981 / 29873 =80.277%
; number reverted decision/ tried decision: 22355 / 30128 =74.200%