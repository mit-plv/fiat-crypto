SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0xa8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x78 ], rbx; saving to stack
mov [ rsp + 0x80 ], rbp; saving to stack
mov [ rsp + 0x88 ], r12; saving to stack
mov [ rsp + 0x90 ], r13; saving to stack
mov [ rsp + 0x98 ], r14; saving to stack
mov [ rsp + 0xa0 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, rax; x2 to rdx
mulx rax, r10, [ rsi + 0x8 ]; x89, x88<- x2 * arg1[1]
mulx r11, rbx, [ rsi + 0x0 ]; x91, x90<- x2 * arg1[0]
test al, al
adox r10, r11
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
mulx r12, r13, [ rsi + 0x18 ]; x85, x84<- x2 * arg1[3]
xchg rdx, rbp; x1, swapping with x2, which is currently in rdx
mulx r14, r15, [ rsi + 0x0 ]; x46, x45<- x1 * arg1[0]
xchg rdx, rbp; x2, swapping with x1, which is currently in rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x87, x86<- x2 * arg1[2]
mov r8, rdx; preserving value of x87 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r9, r11, rbp; x44, x43<- x1 * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r10; spilling x92 to mem
mulx rdi, r10, rbp; x40, x39<- x1 * arg1[3]
adcx r11, r14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbp, r14, rbp; x42, x41<- x1 * arg1[2]
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
adcx r14, r9
adcx r10, rbp
mulx r9, rbp, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
mov [ rsp + 0x10 ], r10; spilling x51 to mem
mov [ rsp + 0x18 ], r14; spilling x49 to mem
mulx r10, r14, [ rsi + 0x0 ]; x136, x135<- x3 * arg1[0]
mov [ rsp + 0x20 ], r14; spilling x135 to mem
mov r14, 0x0 ; moving imm to reg
adcx rdi, r14
adox rcx, rax
mulx rax, r14, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
mov [ rsp + 0x28 ], rcx; spilling x94 to mem
mov rcx, [ rsi + 0x0 ]; load m64 x4 to register64
mov [ rsp + 0x30 ], rdi; spilling x53 to mem
mulx rdx, rdi, [ rsi + 0x18 ]; x130, x129<- x3 * arg1[3]
adox r13, r8
clc;
adcx r14, r10
xchg rdx, rcx; x4, swapping with x130, which is currently in rdx
mulx r8, r10, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
adcx rbp, rax
adcx rdi, r9
mulx r9, rax, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
mov [ rsp + 0x38 ], rdi; spilling x141 to mem
mov [ rsp + 0x40 ], rbp; spilling x139 to mem
mulx rdi, rbp, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
mov [ rsp + 0x48 ], r14; spilling x137 to mem
mov r14, 0x0 ; moving imm to reg
adcx rcx, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r10; x11, swapping with x4, which is currently in rdx
mov [ rsp + 0x50 ], rcx; spilling x143 to mem
mov [ rsp + 0x58 ], r13; spilling x96 to mem
mulx rcx, r13, r14; x25, x24<- x11 * 0xffffffffffffffff
mov r14, 0x0 ; moving imm to reg
adox r12, r14
mov r14, 0xffffffff ; moving imm to reg
mov [ rsp + 0x60 ], r12; spilling x98 to mem
mov [ rsp + 0x68 ], rdi; spilling x8 to mem
mulx r12, rdi, r14; x23, x22<- x11 * 0xffffffff
xor r14, r14
adox r13, rdx
adcx rdi, rcx
setc r13b; spill CF x27 to reg (r13)
clc;
adcx rax, r8
adox rdi, rax
movzx r8, r13b; x28, copying x27 here, cause x27 is needed in a reg for other than x28, namely all: , x28, size: 1
lea r8, [ r8 + r12 ]
adcx rbp, r9
setc r9b; spill CF x16 to reg (r9)
clc;
adcx r15, rdi
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x54, swapping with x11, which is currently in rdx
mulx r12, r13, rcx; x69, x68<- x54 * 0xffffffffffffffff
adox r8, rbp
adcx r11, r8
mov rax, 0xffffffff ; moving imm to reg
mulx rdi, rbp, rax; x67, x66<- x54 * 0xffffffff
mov r8, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r15; x11, swapping with x54, which is currently in rdx
mulx rdx, r14, r8; x21, x20<- x11 * 0xffffffff00000001
setc r8b; spill CF x57 to reg (r8)
clc;
adcx rbp, r12
setc r12b; spill CF x71 to reg (r12)
clc;
adcx r13, r15
adcx rbp, r11
setc r13b; spill CF x76 to reg (r13)
clc;
adcx rbx, rbp
xchg rdx, rcx; 0xffffffffffffffff, swapping with x21, which is currently in rdx
mulx r11, rbp, rbx; x114, x113<- x99 * 0xffffffffffffffff
xchg rdx, r10; x4, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, rax, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
setc r10b; spill CF x100 to reg (r10)
clc;
adcx rbp, rbx
setc bpl; spill CF x119 to reg (rbp)
clc;
mov byte [ rsp + 0x70 ], r10b; spilling byte x100 to mem
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r10; loading flag
adcx rax, [ rsp + 0x68 ]
mov r9, 0x0 ; moving imm to reg
adcx rdx, r9
adox r14, rax
clc;
movzx r8, r8b
adcx r8, r10; loading flag
adcx r14, [ rsp + 0x18 ]
movzx r8, r12b; x72, copying x71 here, cause x71 is needed in a reg for other than x72, namely all: , x72, size: 1
lea r8, [ r8 + rdi ]
adox rcx, rdx
mov rdi, 0xffffffff ; moving imm to reg
mov rdx, rbx; x99 to rdx
mulx rbx, r12, rdi; x112, x111<- x99 * 0xffffffff
setc al; spill CF x59 to reg (rax)
clc;
adcx r12, r11
seto r11b; spill OF x38 to reg (r11)
inc r10; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r9, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r9; loading flag
adox r14, r8
adcx rbx, r10
movzx r13, byte [ rsp + 0x70 ]; load byte memx100 to register64
clc;
adcx r13, r9; loading flag
adcx r14, [ rsp + 0x8 ]
setc r13b; spill CF x102 to reg (r13)
clc;
movzx rax, al
adcx rax, r9; loading flag
adcx rcx, [ rsp + 0x10 ]
movzx r11, r11b
mov rax, [ rsp + 0x30 ]; x62, copying x53 here, cause x53 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adcx rax, r11
setc r8b; spill CF x63 to reg (r8)
clc;
movzx rbp, bpl
adcx rbp, r9; loading flag
adcx r14, r12
mov rbp, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r15; x54, swapping with x99, which is currently in rdx
mulx rdx, r11, rbp; x65, x64<- x54 * 0xffffffff00000001
adox r11, rcx
xchg rdx, rbp; 0xffffffff00000001, swapping with x65, which is currently in rdx
mulx r15, r12, r15; x110, x109<- x99 * 0xffffffff00000001
adox rbp, rax
movzx rcx, r8b; x83, copying x63 here, cause x63 is needed in a reg for other than x83, namely all: , x83, size: 1
adox rcx, r10
inc r9; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r10; loading flag
adox r11, [ rsp + 0x28 ]
mov r13, [ rsp + 0x58 ]; x105, copying x96 here, cause x96 is needed in a reg for other than x105, namely all: , x105--x106, size: 1
adox r13, rbp
mov r8, [ rsp + 0x60 ]; x107, copying x98 here, cause x98 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adox r8, rcx
adcx rbx, r11
seto al; spill OF x108 to reg (rax)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, [ rsp + 0x20 ]
adcx r12, r13
mov rcx, [ rsp + 0x48 ]; x146, copying x137 here, cause x137 is needed in a reg for other than x146, namely all: , x146--x147, size: 1
adox rcx, rbx
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with 0xffffffff00000001, which is currently in rdx
mulx r13, rbx, r14; x159, x158<- x144 * 0xffffffffffffffff
adcx r15, r8
mov r8, [ rsp + 0x40 ]; x148, copying x139 here, cause x139 is needed in a reg for other than x148, namely all: , x148--x149, size: 1
adox r8, r12
xchg rdx, rdi; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r12, r9, r14; x157, x156<- x144 * 0xffffffff
movzx rbp, al; x128, copying x108 here, cause x108 is needed in a reg for other than x128, namely all: , x128, size: 1
mov r10, 0x0 ; moving imm to reg
adcx rbp, r10
clc;
adcx r9, r13
adcx r12, r10
mov rax, [ rsp + 0x38 ]; x150, copying x141 here, cause x141 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adox rax, r15
clc;
adcx rbx, r14
mov rbx, [ rsp + 0x50 ]; x152, copying x143 here, cause x143 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox rbx, rbp
xchg rdx, r11; 0xffffffff00000001, swapping with 0xffffffff, which is currently in rdx
mulx r14, r13, r14; x155, x154<- x144 * 0xffffffff00000001
adcx r9, rcx
adcx r12, r8
setc cl; spill CF x168 to reg (rcx)
seto r15b; spill OF x153 to reg (r15)
mov r8, r9; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
sub r8, rdi
mov rbp, r12; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
sbb rbp, r11
dec r10; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rcx, cl
adox rcx, r10; loading flag
adox rax, r13
adox r14, rbx
movzx rbx, r15b; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
mov r13, 0x0 ; moving imm to reg
adox rbx, r13
mov r15, rax; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r15, 0x00000000
mov rcx, r14; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
sbb rcx, rdx
sbb rbx, 0x00000000
cmovc rbp, r12; if CF, x185<- x167 (nzVar)
cmovc r8, r9; if CF, x184<- x165 (nzVar)
cmovc rcx, r14; if CF, x187<- x171 (nzVar)
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbx + 0x0 ], r8; out1[0] = x184
cmovc r15, rax; if CF, x186<- x169 (nzVar)
mov [ rbx + 0x8 ], rbp; out1[1] = x185
mov [ rbx + 0x18 ], rcx; out1[3] = x187
mov [ rbx + 0x10 ], r15; out1[2] = x186
mov rbx, [ rsp + 0x78 ]; restoring from stack
mov rbp, [ rsp + 0x80 ]; restoring from stack
mov r12, [ rsp + 0x88 ]; restoring from stack
mov r13, [ rsp + 0x90 ]; restoring from stack
mov r14, [ rsp + 0x98 ]; restoring from stack
mov r15, [ rsp + 0xa0 ]; restoring from stack
add rsp, 0xa8 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 74.29, best 53.14492753623188, lastGood 54.52173913043478
; seed 2165586197121668 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 634766 ms / 60000 runs=> 10.579433333333334ms/run
; Time spent for assembling and measureing (initial batch_size=138, initial num_batches=101): 157898 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2487499330461934
; number reverted permutation/ tried permutation: 25036 / 29947 =83.601%
; number reverted decision/ tried decision: 22006 / 30054 =73.222%