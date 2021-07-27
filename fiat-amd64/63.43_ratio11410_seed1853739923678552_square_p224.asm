SECTION .text
	GLOBAL square_p224
square_p224:
sub rsp, 0xb8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x88 ], rbx; saving to stack
mov [ rsp + 0x90 ], rbp; saving to stack
mov [ rsp + 0x98 ], r12; saving to stack
mov [ rsp + 0xa0 ], r13; saving to stack
mov [ rsp + 0xa8 ], r14; saving to stack
mov [ rsp + 0xb0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, rax; x12, x11<- x4 * arg1[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r12, rax; x6, x5<- x4 * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r14, rax; x10, x9<- x4 * arg1[1]
test al, al
adox r14, r11
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r15, rax; x8, x7<- x4 * arg1[2]
mov rdx, r10; x2 to rdx
mulx r10, rcx, [ rsi + 0x0 ]; x99, x98<- x2 * arg1[0]
adox r15, r13
mulx r8, r9, [ rsi + 0x10 ]; x95, x94<- x2 * arg1[2]
adox r12, rax
mov r11, [ rsi + 0x18 ]; load m64 x3 to register64
mov r13, [ rsi + 0x8 ]; load m64 x1 to register64
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rax, rdi, [ rsi + 0x8 ]; x97, x96<- x2 * arg1[1]
adcx rdi, r10
adcx r9, rax
mulx rdx, r10, [ rsi + 0x18 ]; x93, x92<- x2 * arg1[3]
adcx r10, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffffffffffff, swapping with x93, which is currently in rdx
mov [ rsp + 0x8 ], r10; spilling x104 to mem
mulx rax, r10, rbx; _, x20<- x11 * 0xffffffffffffffff
mov [ rsp + 0x10 ], r9; spilling x102 to mem
mulx rax, r9, r10; x25, x24<- x20 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
adcx r8, rdx
adox rbp, rdx
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x18 ], r8; spilling x106 to mem
mov [ rsp + 0x20 ], r11; spilling x3 to mem
mulx r8, r11, r10; x27, x26<- x20 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x28 ], rdi; spilling x100 to mem
mov [ rsp + 0x30 ], rcx; spilling x98 to mem
mulx rdi, rcx, r10; x23, x22<- x20 * 0xffffffff
xor rdx, rdx
adox r10, rbx
xchg rdx, r13; x1, swapping with 0x0, which is currently in rdx
mulx r10, rbx, [ rsi + 0x0 ]; x50, x49<- x1 * arg1[0]
adcx r9, r8
adcx rcx, rax
adox r11, r14
adcx rdi, r13
adox r9, r15
clc;
adcx rbx, r11
mulx r14, r15, [ rsi + 0x8 ]; x48, x47<- x1 * arg1[1]
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x58, swapping with x1, which is currently in rdx
mulx r8, r11, rax; _, x68<- x58 * 0xffffffffffffffff
mov r8, rdx; preserving value of x58 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r13, rax, rbx; x46, x45<- x1 * arg1[2]
mov rdx, r11; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x70--x71, _--x82, x72--x73, x74--x75, size: 4
mov [ rsp + 0x38 ], r13; spilling x46 to mem
seto r13b; spill OF x38 to reg (r13)
mov [ rsp + 0x40 ], rdi; spilling x32 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdx, r8
seto dl; spill OF x82 to reg (rdx)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, r10
mov r10, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r10; 0xffffffff00000000, swapping with x82, which is currently in rdx
mulx r8, rdi, r11; x75, x74<- x68 * 0xffffffff00000000
adcx r15, r9
adox rax, r14
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x68, swapping with 0xffffffff00000000, which is currently in rdx
mulx r14, r11, r9; x73, x72<- x68 * 0xffffffffffffffff
seto r9b; spill OF x54 to reg (r9)
mov [ rsp + 0x48 ], r14; spilling x73 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox r12, rcx
mov rcx, [ rsp + 0x40 ]; x41, copying x32 here, cause x32 is needed in a reg for other than x41, namely all: , x41--x42, size: 1
adox rcx, rbp
adcx rax, r12
seto bpl; spill OF x42 to reg (rbp)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r13; loading flag
adox r15, rdi
setc r10b; spill CF x63 to reg (r10)
clc;
adcx r11, r8
xchg rdx, rbx; x1, swapping with x68, which is currently in rdx
mulx rdx, r8, [ rsi + 0x18 ]; x44, x43<- x1 * arg1[3]
setc dil; spill CF x77 to reg (rdi)
clc;
movzx r9, r9b
adcx r9, r13; loading flag
adcx r8, [ rsp + 0x38 ]
adcx rdx, r14
clc;
movzx r10, r10b
adcx r10, r13; loading flag
adcx rcx, r8
movzx r9, bpl; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adcx r9, rdx
mov r12, 0xffffffff ; moving imm to reg
mov rdx, rbx; x68 to rdx
mulx rdx, rbx, r12; x71, x70<- x68 * 0xffffffff
setc bpl; spill CF x67 to reg (rbp)
clc;
movzx rdi, dil
adcx rdi, r13; loading flag
adcx rbx, [ rsp + 0x48 ]
adcx rdx, r14
adox r11, rax
clc;
adcx r15, [ rsp + 0x30 ]
mov r10, [ rsp + 0x28 ]; x109, copying x100 here, cause x100 is needed in a reg for other than x109, namely all: , x109--x110, size: 1
adcx r10, r11
adox rbx, rcx
adox rdx, r9
movzx rax, bpl; x91, copying x67 here, cause x67 is needed in a reg for other than x91, namely all: , x91, size: 1
adox rax, r14
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x89, which is currently in rdx
mulx r8, rcx, r15; _, x117<- x107 * 0xffffffffffffffff
mov r8, rcx; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x119--x120, _--x131, x121--x122, x123--x124, size: 4
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r15
mov r8, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsp + 0x20 ]; saving x3 in rdx.
mulx r9, r11, [ rsi + 0x0 ]; x148, x147<- x3 * arg1[0]
mov r15, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r15; 0xffffffff00000000, swapping with x3, which is currently in rdx
mulx r14, rbp, rcx; x124, x123<- x117 * 0xffffffff00000000
adox rbp, r10
seto r10b; spill OF x133 to reg (r10)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rbp
mov rbp, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r13, r12, r15; x146, x145<- x3 * arg1[1]
mov rdx, r11; x156 to rdx
mulx r11, rbp, r8; _, x166<- x156 * 0xffffffffffffffff
mov r11, [ rsp + 0x10 ]; x111, copying x102 here, cause x102 is needed in a reg for other than x111, namely all: , x111--x112, size: 1
adcx r11, rbx
setc bl; spill CF x112 to reg (rbx)
clc;
adcx r12, r9
xchg rdx, r8; 0xffffffffffffffff, swapping with x156, which is currently in rdx
mov [ rsp + 0x50 ], r13; spilling x146 to mem
mulx r9, r13, rcx; x122, x121<- x117 * 0xffffffffffffffff
setc dl; spill CF x150 to reg (rdx)
clc;
adcx r13, r14
mov r14, 0xffffffff ; moving imm to reg
xchg rdx, rcx; x117, swapping with x150, which is currently in rdx
mov byte [ rsp + 0x58 ], cl; spilling byte x150 to mem
mulx rdx, rcx, r14; x120, x119<- x117 * 0xffffffff
mov r14, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r14; 0xffffffff00000000, swapping with x120, which is currently in rdx
mov [ rsp + 0x60 ], rax; spilling x91 to mem
mov [ rsp + 0x68 ], r14; spilling x120 to mem
mulx rax, r14, rbp; x173, x172<- x166 * 0xffffffff00000000
xchg rdx, r15; x3, swapping with 0xffffffff00000000, which is currently in rdx
mov [ rsp + 0x70 ], rax; spilling x173 to mem
mulx r15, rax, [ rsi + 0x10 ]; x144, x143<- x3 * arg1[2]
mov [ rsp + 0x78 ], r15; spilling x144 to mem
setc r15b; spill CF x126 to reg (r15)
clc;
mov [ rsp + 0x80 ], rax; spilling x143 to mem
mov rax, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rax; loading flag
adcx r11, r13
adox r12, r11
mov r10, rbp; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , _--x180, x168--x169, x170--x171, size: 3
setc r13b; spill CF x135 to reg (r13)
clc;
adcx r10, r8
seto r10b; spill OF x159 to reg (r10)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r8; loading flag
adox rdi, [ rsp + 0x8 ]
adcx r14, r12
setc bl; spill CF x182 to reg (rbx)
clc;
movzx r15, r15b
adcx r15, r8; loading flag
adcx r9, rcx
mov r15, [ rsp + 0x68 ]; x129, copying x120 here, cause x120 is needed in a reg for other than x129, namely all: , x129, size: 1
adcx r15, rax
clc;
movzx r13, r13b
adcx r13, r8; loading flag
adcx rdi, r9
mov rcx, [ rsp + 0x18 ]; load m64 x106 to register64
mov r11, [ rsp + 0x60 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adox r11, rcx
adcx r15, r11
mov rcx, [ rsp + 0x80 ]; load m64 x143 to register64
setc r13b; spill CF x139 to reg (r13)
movzx r12, byte [ rsp + 0x58 ]; load byte memx150 to register64
clc;
adcx r12, r8; loading flag
adcx rcx, [ rsp + 0x50 ]
mulx rdx, r12, [ rsi + 0x18 ]; x142, x141<- x3 * arg1[3]
mov r9, [ rsp + 0x78 ]; x153, copying x144 here, cause x144 is needed in a reg for other than x153, namely all: , x153--x154, size: 1
adcx r9, r12
movzx r11, r13b; x140, copying x139 here, cause x139 is needed in a reg for other than x140, namely all: , x140, size: 1
adox r11, rax
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x142, which is currently in rdx
mulx r12, rax, rbp; x171, x170<- x166 * 0xffffffffffffffff
adc r13, 0x0
add r10b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r10b; since that has deps, resore it whereever it was
adox rdi, rcx
mov r10, 0xffffffff ; moving imm to reg
xchg rdx, r10; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbp, rcx, rbp; x169, x168<- x166 * 0xffffffff
adox r9, r15
adcx rax, [ rsp + 0x70 ]
adcx rcx, r12
mov r15, 0x0 ; moving imm to reg
adcx rbp, r15
clc;
movzx rbx, bl
adcx rbx, r8; loading flag
adcx rdi, rax
adox r13, r11
adcx rcx, r9
adcx rbp, r13
seto bl; spill OF x189 to reg (rbx)
adc bl, 0x0
movzx rbx, bl
mov r11, r14; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x200, x190--x191, size: 2
sub r11, 0x00000001
mov r12, rdi; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r9, 0xffffffff00000000 ; moving imm to reg
sbb r12, r9
mov rax, rcx; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x202, x194--x195, size: 2
sbb rax, r10
mov r13, rbp; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
sbb r13, rdx
movzx r8, bl; _, copying x189 here, cause x189 is needed in a reg for other than _, namely all: , _--x199, size: 1
sbb r8, 0x00000000
cmovc rax, rcx; if CF, x202<- x185 (nzVar)
cmovc r12, rdi; if CF, x201<- x183 (nzVar)
cmovc r13, rbp; if CF, x203<- x187 (nzVar)
cmovc r11, r14; if CF, x200<- x181 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x0 ], r11; out1[0] = x200
mov [ r8 + 0x18 ], r13; out1[3] = x203
mov [ r8 + 0x8 ], r12; out1[1] = x201
mov [ r8 + 0x10 ], rax; out1[2] = x202
mov rbx, [ rsp + 0x88 ]; restoring from stack
mov rbp, [ rsp + 0x90 ]; restoring from stack
mov r12, [ rsp + 0x98 ]; restoring from stack
mov r13, [ rsp + 0xa0 ]; restoring from stack
mov r14, [ rsp + 0xa8 ]; restoring from stack
mov r15, [ rsp + 0xb0 ]; restoring from stack
add rsp, 0xb8 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 80.94, best 62.86764705882353, lastGood 63.4264705882353
; seed 1853739923678552 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 667491 ms / 60000 runs=> 11.12485ms/run
; Time spent for assembling and measureing (initial batch_size=136, initial num_batches=101): 151065 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2263176582156164
; number reverted permutation/ tried permutation: 25477 / 30040 =84.810%
; number reverted decision/ tried decision: 21918 / 29961 =73.155%