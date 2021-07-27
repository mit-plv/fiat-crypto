SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0xd8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xa8 ], rbx; saving to stack
mov [ rsp + 0xb0 ], rbp; saving to stack
mov [ rsp + 0xb8 ], r12; saving to stack
mov [ rsp + 0xc0 ], r13; saving to stack
mov [ rsp + 0xc8 ], r14; saving to stack
mov [ rsp + 0xd0 ], r15; saving to stack
mov rax, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, rax; x107, x106<- x2 * arg1[0]
mov rbx, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x2 to rdx
mulx rax, rbp, [ rsi + 0x8 ]; x105, x104<- x2 * arg1[1]
mulx r12, r13, [ rsi + 0x10 ]; x103, x102<- x2 * arg1[2]
test al, al
adox rbp, r10
adox r13, rax
xchg rdx, rbx; x4, swapping with x2, which is currently in rdx
mulx r14, r15, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mov rcx, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r15; x11, swapping with x4, which is currently in rdx
mulx r8, r9, rcx; _, x20<- x11 * 0xd838091dd2253531
mov r8, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r8; 0xfffffffefffffc2f, swapping with x11, which is currently in rdx
mulx r10, rax, r9; x29, x28<- x20 * 0xfffffffefffffc2f
xchg rdx, rbx; x2, swapping with 0xfffffffefffffc2f, which is currently in rdx
mulx rdx, rbx, [ rsi + 0x18 ]; x101, x100<- x2 * arg1[3]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x101, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r13; spilling x110 to mem
mulx rdi, r13, r9; x27, x26<- x20 * 0xffffffffffffffff
adox rbx, r12
mov r12, 0x0 ; moving imm to reg
adox rcx, r12
mov [ rsp + 0x10 ], rcx; spilling x114 to mem
mulx r12, rcx, r9; x25, x24<- x20 * 0xffffffffffffffff
mov [ rsp + 0x18 ], rbx; spilling x112 to mem
mulx r9, rbx, r9; x23, x22<- x20 * 0xffffffffffffffff
adcx r13, r10
adcx rcx, rdi
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rbx, r12
xchg rdx, r15; x4, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdi, r12, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
adc r9, 0x0
test al, al
adox rax, r8
adcx r12, r14
xchg rdx, r10; x1, swapping with x4, which is currently in rdx
mulx rax, r14, [ rsi + 0x0 ]; x54, x53<- x1 * arg1[0]
adox r13, r12
setc r8b; spill CF x14 to reg (r8)
clc;
adcx r14, r13
mov r12, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r14; x62, swapping with x1, which is currently in rdx
mulx r13, r15, r12; _, x72<- x62 * 0xd838091dd2253531
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x72, swapping with x62, which is currently in rdx
mov [ rsp + 0x20 ], r9; spilling x36 to mem
mulx r12, r9, r13; x75, x74<- x72 * 0xffffffffffffffff
mov r13, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x28 ], rbp; spilling x108 to mem
mov [ rsp + 0x30 ], rbx; spilling x34 to mem
mulx rbp, rbx, r13; x81, x80<- x72 * 0xfffffffefffffc2f
mov r13, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x38 ], r11; spilling x106 to mem
mov [ rsp + 0x40 ], rbx; spilling x80 to mem
mulx r11, rbx, r13; x79, x78<- x72 * 0xffffffffffffffff
mov [ rsp + 0x48 ], rcx; spilling x32 to mem
mulx rdx, rcx, r13; x77, x76<- x72 * 0xffffffffffffffff
setc r13b; spill CF x63 to reg (r13)
clc;
adcx rbx, rbp
xchg rdx, r10; x4, swapping with x77, which is currently in rdx
mov [ rsp + 0x50 ], rbx; spilling x82 to mem
mulx rbp, rbx, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
adcx rcx, r11
adcx r9, r10
mov r11, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x58 ], r9; spilling x86 to mem
mulx r10, r9, r14; x52, x51<- x1 * arg1[1]
mov rdx, 0x0 ; moving imm to reg
adcx r12, rdx
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx rdi, rbx
setc r8b; spill CF x16 to reg (r8)
clc;
adcx r9, rax
mov rax, [ rsp + 0x48 ]; x41, copying x32 here, cause x32 is needed in a reg for other than x41, namely all: , x41--x42, size: 1
adox rax, rdi
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, rdi, r14; x50, x49<- x1 * arg1[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x60 ], r12; spilling x88 to mem
mulx r11, r12, r11; x6, x5<- x4 * arg1[3]
setc dl; spill CF x56 to reg (rdx)
clc;
mov [ rsp + 0x68 ], r11; spilling x6 to mem
mov r11, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r11; loading flag
adcx rax, r9
setc r13b; spill CF x65 to reg (r13)
clc;
adcx r15, [ rsp + 0x40 ]
mov r15, [ rsp + 0x50 ]; x91, copying x82 here, cause x82 is needed in a reg for other than x91, namely all: , x91--x92, size: 1
adcx r15, rax
setc r9b; spill CF x92 to reg (r9)
clc;
adcx r15, [ rsp + 0x38 ]
setc al; spill CF x116 to reg (rax)
clc;
movzx rdx, dl
adcx rdx, r11; loading flag
adcx r10, rdi
setc dl; spill CF x58 to reg (rdx)
clc;
movzx r8, r8b
adcx r8, r11; loading flag
adcx rbp, r12
mov r8, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r8; 0xd838091dd2253531, swapping with x58, which is currently in rdx
mulx rdi, r12, r15; _, x125<- x115 * 0xd838091dd2253531
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x125, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0x70 ], rbx; spilling x50 to mem
mulx r12, rbx, r11; x132, x131<- x125 * 0xffffffffffffffff
mov r11, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x78 ], r12; spilling x132 to mem
mov byte [ rsp + 0x80 ], r8b; spilling byte x58 to mem
mulx r12, r8, r11; x134, x133<- x125 * 0xfffffffefffffc2f
mov r11, [ rsp + 0x30 ]; x43, copying x34 here, cause x34 is needed in a reg for other than x43, namely all: , x43--x44, size: 1
adox r11, rbp
setc bpl; spill CF x18 to reg (rbp)
clc;
adcx rbx, r12
setc r12b; spill CF x136 to reg (r12)
clc;
mov byte [ rsp + 0x88 ], bpl; spilling byte x18 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r11, r10
setc r13b; spill CF x67 to reg (r13)
clc;
adcx r8, r15
setc r8b; spill CF x143 to reg (r8)
clc;
movzx r9, r9b
adcx r9, rbp; loading flag
adcx r11, rcx
setc cl; spill CF x94 to reg (rcx)
clc;
movzx rax, al
adcx rax, rbp; loading flag
adcx r11, [ rsp + 0x28 ]
setc r9b; spill CF x118 to reg (r9)
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r11, rbx
mov r15, rdx; preserving value of x125 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r14, rax, r14; x48, x47<- x1 * arg1[3]
setc dl; spill CF x145 to reg (rdx)
movzx r10, byte [ rsp + 0x80 ]; load byte memx58 to register64
clc;
adcx r10, rbp; loading flag
adcx rax, [ rsp + 0x70 ]
movzx r10, byte [ rsp + 0x88 ]; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov rbx, [ rsp + 0x68 ]; load m64 x6 to register64
lea r10, [ r10 + rbx ]; r8/64 + m8
mov rbx, [ rsp + 0x20 ]; x45, copying x36 here, cause x36 is needed in a reg for other than x45, namely all: , x45--x46, size: 1
adox rbx, r10
mov r8, 0x0 ; moving imm to reg
adcx r14, r8
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx rbx, rax
setc r13b; spill CF x69 to reg (r13)
clc;
movzx rcx, cl
adcx rcx, rbp; loading flag
adcx rbx, [ rsp + 0x58 ]
movzx rcx, r13b; x70, copying x69 here, cause x69 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adox rcx, r14
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x125, swapping with x145, which is currently in rdx
mulx r10, r14, rax; x130, x129<- x125 * 0xffffffffffffffff
setc r13b; spill CF x96 to reg (r13)
clc;
movzx r9, r9b
adcx r9, rbp; loading flag
adcx rbx, [ rsp + 0x8 ]
mulx rdx, r9, rax; x128, x127<- x125 * 0xffffffffffffffff
seto r8b; spill OF x71 to reg (r8)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbp; loading flag
adox r14, [ rsp + 0x78 ]
adox r9, r10
mov r12, 0x0 ; moving imm to reg
adox rdx, r12
mov r10, [ rsi + 0x18 ]; load m64 x3 to register64
dec r12; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r15, r15b
adox r15, r12; loading flag
adox rbx, r14
xchg rdx, r10; x3, swapping with x141, which is currently in rdx
mulx rbp, r15, [ rsi + 0x0 ]; x160, x159<- x3 * arg1[0]
setc r14b; spill CF x120 to reg (r14)
clc;
movzx r13, r13b
adcx r13, r12; loading flag
adcx rcx, [ rsp + 0x60 ]
movzx r13, r8b; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
mov r12, 0x0 ; moving imm to reg
adcx r13, r12
clc;
mov r8, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r8; loading flag
adcx rcx, [ rsp + 0x18 ]
mov r14, [ rsp + 0x10 ]; x123, copying x114 here, cause x114 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adcx r14, r13
adox r9, rcx
adox r10, r14
seto r13b; spill OF x151 to reg (r13)
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, r11
mov r11, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r11; 0xd838091dd2253531, swapping with x3, which is currently in rdx
mulx r14, r12, r15; _, x178<- x168 * 0xd838091dd2253531
mov r14, rdx; preserving value of 0xd838091dd2253531 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r8, r11; x158, x157<- x3 * arg1[1]
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mulx rax, r14, r12; x187, x186<- x178 * 0xfffffffefffffc2f
xchg rdx, r11; x3, swapping with 0xfffffffefffffc2f, which is currently in rdx
mov [ rsp + 0x90 ], r10; spilling x150 to mem
mulx r11, r10, [ rsi + 0x10 ]; x156, x155<- x3 * arg1[2]
mov [ rsp + 0x98 ], r11; spilling x156 to mem
movzx r11, r13b; x152, copying x151 here, cause x151 is needed in a reg for other than x152, namely all: , x152, size: 1
mov [ rsp + 0xa0 ], r9; spilling x148 to mem
mov r9, 0x0 ; moving imm to reg
adcx r11, r9
clc;
adcx r14, r15
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x178, swapping with x3, which is currently in rdx
mulx r13, r15, r14; x181, x180<- x178 * 0xffffffffffffffff
setc r14b; spill CF x196 to reg (r14)
clc;
adcx r8, rbp
adcx r10, rcx
mov rbp, 0xffffffffffffffff ; moving imm to reg
mulx rcx, r9, rbp; x185, x184<- x178 * 0xffffffffffffffff
adox r8, rbx
setc bl; spill CF x164 to reg (rbx)
clc;
adcx r9, rax
mulx rdx, rax, rbp; x183, x182<- x178 * 0xffffffffffffffff
adcx rax, rcx
mov rcx, [ rsp + 0xa0 ]; x172, copying x148 here, cause x148 is needed in a reg for other than x172, namely all: , x172--x173, size: 1
adox rcx, r10
mov r10, rdx; preserving value of x183 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r12, rbp, r12; x154, x153<- x3 * arg1[3]
adcx r15, r10
mov rdx, 0x0 ; moving imm to reg
adcx r13, rdx
clc;
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r10; loading flag
adcx rbp, [ rsp + 0x98 ]
adcx r12, rdx
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx r8, r9
mov r14, [ rsp + 0x90 ]; x174, copying x150 here, cause x150 is needed in a reg for other than x174, namely all: , x174--x175, size: 1
adox r14, rbp
adcx rax, rcx
adox r12, r11
adcx r15, r14
adcx r13, r12
setc r11b; spill CF x204 to reg (r11)
seto bl; spill OF x177 to reg (rbx)
mov r9, r8; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov rcx, 0xfffffffefffffc2f ; moving imm to reg
sub r9, rcx
mov rbp, rax; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
mov r14, 0xffffffffffffffff ; moving imm to reg
sbb rbp, r14
movzx r12, r11b; x205, copying x204 here, cause x204 is needed in a reg for other than x205, namely all: , x205, size: 1
movzx rbx, bl
lea r12, [ r12 + rbx ]
mov rbx, r15; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb rbx, r14
mov r11, r13; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x212--x213, x219, size: 2
sbb r11, r14
sbb r12, 0x00000000
cmovc r11, r13; if CF, x219<- x203 (nzVar)
cmovc rbp, rax; if CF, x217<- x199 (nzVar)
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x8 ], rbp; out1[1] = x217
cmovc rbx, r15; if CF, x218<- x201 (nzVar)
mov [ r12 + 0x18 ], r11; out1[3] = x219
cmovc r9, r8; if CF, x216<- x197 (nzVar)
mov [ r12 + 0x10 ], rbx; out1[2] = x218
mov [ r12 + 0x0 ], r9; out1[0] = x216
mov rbx, [ rsp + 0xa8 ]; restoring from stack
mov rbp, [ rsp + 0xb0 ]; restoring from stack
mov r12, [ rsp + 0xb8 ]; restoring from stack
mov r13, [ rsp + 0xc0 ]; restoring from stack
mov r14, [ rsp + 0xc8 ]; restoring from stack
mov r15, [ rsp + 0xd0 ]; restoring from stack
add rsp, 0xd8 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 3620 MHz
; first cyclecount 92.34, best 73.55963302752293, lastGood 74.63063063063063
; seed 3879384365785814 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 754168 ms / 60000 runs=> 12.569466666666667ms/run
; Time spent for assembling and measureing (initial batch_size=110, initial num_batches=101): 133120 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.17651239511620753
; number reverted permutation/ tried permutation: 25900 / 29918 =86.570%
; number reverted decision/ tried decision: 21383 / 30083 =71.080%