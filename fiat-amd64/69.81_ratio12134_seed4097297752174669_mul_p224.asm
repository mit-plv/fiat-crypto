SECTION .text
	GLOBAL mul_p224
mul_p224:
sub rsp, 0xf0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xc0 ], rbx; saving to stack
mov [ rsp + 0xc8 ], rbp; saving to stack
mov [ rsp + 0xd0 ], r12; saving to stack
mov [ rsp + 0xd8 ], r13; saving to stack
mov [ rsp + 0xe0 ], r14; saving to stack
mov [ rsp + 0xe8 ], r15; saving to stack
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x18 ]; saving arg2[3] in rdx.
mulx rbx, rbp, rax; x142, x141<- x3 * arg2[3]
mov rdx, rax; x3 to rdx
mulx rax, r12, [ r11 + 0x8 ]; x146, x145<- x3 * arg2[1]
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx r14, r15, r10; x48, x47<- x1 * arg2[1]
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx rcx, r8, r13; x148, x147<- x3 * arg2[0]
mov rdx, r10; x1 to rdx
mulx r10, r9, [ r11 + 0x0 ]; x50, x49<- x1 * arg2[0]
xchg rdx, r13; x3, swapping with x1, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rdx, rdi, [ r11 + 0x10 ]; x144, x143<- x3 * arg2[2]
mov [ rsp + 0x8 ], r8; spilling x147 to mem
xor r8, r8
adox r15, r10
mov r10, rdx; preserving value of x144 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x10 ], r15; spilling x51 to mem
mulx r8, r15, r13; x46, x45<- x1 * arg2[2]
adcx r12, rcx
mov rcx, [ rsi + 0x0 ]; load m64 x4 to register64
adox r15, r14
adcx rdi, rax
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mulx r13, rax, r13; x44, x43<- x1 * arg2[3]
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x18 ], rdi; spilling x151 to mem
mulx r14, rdi, rcx; x12, x11<- x4 * arg2[0]
mov [ rsp + 0x20 ], r12; spilling x149 to mem
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mov [ rsp + 0x28 ], r15; spilling x53 to mem
mulx r12, r15, rdi; _, x20<- x11 * 0xffffffffffffffff
adox rax, r8
adcx rbp, r10
mov r12, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx r10, r8, rcx; x10, x9<- x4 * arg2[1]
mov r12, 0xffffffff00000000 ; moving imm to reg
mov rdx, r12; 0xffffffff00000000 to rdx
mov [ rsp + 0x30 ], rbp; spilling x153 to mem
mulx r12, rbp, r15; x27, x26<- x20 * 0xffffffff00000000
mov rdx, 0x0 ; moving imm to reg
adox r13, rdx
adc rbx, 0x0
mov [ rsp + 0x38 ], rbx; spilling x155 to mem
mov rbx, r15; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x22--x23, x24--x25, _--x34, size: 3
test al, al
adox rbx, rdi
adcx r8, r14
adox rbp, r8
mov rbx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mulx r14, rdi, rcx; x8, x7<- x4 * arg2[2]
adcx rdi, r10
setc r10b; spill CF x16 to reg (r10)
clc;
adcx r9, rbp
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r8, rbp, r9; _, x68<- x58 * 0xffffffffffffffff
mulx r8, rbx, r15; x25, x24<- x20 * 0xffffffffffffffff
setc dl; spill CF x59 to reg (rdx)
clc;
adcx rbx, r12
adox rbx, rdi
mov r12, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r12; 0xffffffff00000000, swapping with x59, which is currently in rdx
mov [ rsp + 0x40 ], rsi; spilling arg1 to mem
mulx rdi, rsi, rbp; x75, x74<- x68 * 0xffffffff00000000
xchg rdx, rcx; x4, swapping with 0xffffffff00000000, which is currently in rdx
mulx rdx, rcx, [ r11 + 0x18 ]; x6, x5<- x4 * arg2[3]
mov [ rsp + 0x48 ], r13; spilling x57 to mem
seto r13b; spill OF x38 to reg (r13)
mov [ rsp + 0x50 ], rax; spilling x55 to mem
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rax; loading flag
adox r14, rcx
mov r10, rbp; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x72--x73, x70--x71, _--x82, size: 3
setc cl; spill CF x29 to reg (rcx)
clc;
adcx r10, r9
seto r10b; spill OF x18 to reg (r10)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r9; loading flag
adox rbx, [ rsp + 0x10 ]
movzx r12, r10b; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
lea r12, [ r12 + rdx ]
adcx rsi, rbx
mov rdx, 0xffffffff ; moving imm to reg
mulx r15, r10, r15; x23, x22<- x20 * 0xffffffff
setc bl; spill CF x84 to reg (rbx)
clc;
movzx rcx, cl
adcx rcx, r9; loading flag
adcx r8, r10
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with 0xffffffff, which is currently in rdx
mulx r10, rax, rbp; x73, x72<- x68 * 0xffffffffffffffff
xchg rdx, rcx; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbp, r9, rbp; x71, x70<- x68 * 0xffffffff
mov rdx, 0x0 ; moving imm to reg
adcx r15, rdx
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rdx; loading flag
adcx r14, r8
mov r13, [ rsp + 0x28 ]; x62, copying x53 here, cause x53 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox r13, r14
adcx r15, r12
setc r12b; spill CF x42 to reg (r12)
clc;
adcx rax, rdi
setc dil; spill CF x77 to reg (rdi)
clc;
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r13, rax
mov rbx, [ rsp + 0x50 ]; x64, copying x55 here, cause x55 is needed in a reg for other than x64, namely all: , x64--x65, size: 1
adox rbx, r15
movzx r12, r12b
mov r8, [ rsp + 0x48 ]; x66, copying x57 here, cause x57 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox r8, r12
seto r14b; spill OF x67 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r12; loading flag
adox r10, r9
adcx r10, rbx
mov r9, [ rsp + 0x40 ]; load m64 arg1 to register64
mov r15, [ r9 + 0x10 ]; load m64 x2 to register64
xchg rdx, r15; x2, swapping with 0x0, which is currently in rdx
mulx rax, rdi, [ r11 + 0x0 ]; x99, x98<- x2 * arg2[0]
adox rbp, r15
adcx rbp, r8
mov rbx, -0x3 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdi, rsi
movzx rsi, r14b; x91, copying x67 here, cause x67 is needed in a reg for other than x91, namely all: , x91, size: 1
adcx rsi, r15
mulx r14, r8, [ r11 + 0x8 ]; x97, x96<- x2 * arg2[1]
clc;
adcx r8, rax
xchg rdx, rcx; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx rax, r15, rdi; _, x117<- x107 * 0xffffffffffffffff
mov rax, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r15; x117, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbx, r12, rax; x124, x123<- x117 * 0xffffffff00000000
mov rax, rdx; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x119--x120, _--x131, x121--x122, size: 3
setc r15b; spill CF x101 to reg (r15)
clc;
adcx rax, rdi
adox r8, r13
adcx r12, r8
setc al; spill CF x133 to reg (rax)
clc;
adcx r12, [ rsp + 0x8 ]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r13; 0xffffffffffffffff, swapping with x117, which is currently in rdx
mulx rdi, r8, r12; _, x166<- x156 * 0xffffffffffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x58 ], al; spilling byte x133 to mem
mov [ rsp + 0x60 ], rsi; spilling x91 to mem
mulx rax, rsi, r8; x173, x172<- x166 * 0xffffffff00000000
xchg rdx, rcx; x2, swapping with 0xffffffff00000000, which is currently in rdx
mov [ rsp + 0x68 ], rsi; spilling x172 to mem
mulx rcx, rsi, [ r11 + 0x18 ]; x93, x92<- x2 * arg2[3]
mov [ rsp + 0x70 ], rcx; spilling x93 to mem
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffff, swapping with x2, which is currently in rdx
mov [ rsp + 0x78 ], rbp; spilling x89 to mem
mov [ rsp + 0x80 ], r10; spilling x87 to mem
mulx rbp, r10, r8; x169, x168<- x166 * 0xffffffff
mov [ rsp + 0x88 ], rbp; spilling x169 to mem
mov rbp, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x90 ], rbx; spilling x124 to mem
mulx rcx, rbx, rcx; x95, x94<- x2 * arg2[2]
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; x117 to rdx
mov [ rsp + 0x98 ], rsi; spilling x92 to mem
mulx r13, rsi, rbp; x122, x121<- x117 * 0xffffffffffffffff
xchg rdx, rbp; 0xffffffffffffffff, swapping with x117, which is currently in rdx
mov [ rsp + 0xa0 ], r13; spilling x122 to mem
mov [ rsp + 0xa8 ], rsi; spilling x121 to mem
mulx r13, rsi, r8; x171, x170<- x166 * 0xffffffffffffffff
setc dl; spill CF x157 to reg (rdx)
clc;
adcx rsi, rax
seto al; spill OF x110 to reg (rax)
mov [ rsp + 0xb0 ], rsi; spilling x174 to mem
mov rsi, 0x0 ; moving imm to reg
dec rsi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rsi; loading flag
adox r14, rbx
adcx r10, r13
mov r15, [ rsp + 0x98 ]; x104, copying x92 here, cause x92 is needed in a reg for other than x104, namely all: , x104--x105, size: 1
adox r15, rcx
mov rcx, [ rsp + 0x90 ]; load m64 x124 to register64
seto bl; spill OF x105 to reg (rbx)
inc rsi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0xa8 ]
mov r13, 0xffffffff ; moving imm to reg
xchg rdx, rbp; x117, swapping with x157, which is currently in rdx
mulx rdx, rsi, r13; x120, x119<- x117 * 0xffffffff
mov r13, [ rsp + 0x88 ]; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178, size: 1
mov [ rsp + 0xb8 ], r10; spilling x176 to mem
mov r10, 0x0 ; moving imm to reg
adcx r13, r10
clc;
mov r10, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r10; loading flag
adcx r14, [ rsp + 0x80 ]
mov rax, [ rsp + 0x78 ]; x113, copying x89 here, cause x89 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adcx rax, r15
mov r15, [ rsp + 0xa0 ]; x127, copying x122 here, cause x122 is needed in a reg for other than x127, namely all: , x127--x128, size: 1
adox r15, rsi
movzx rsi, bl; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, size: 1
mov r10, [ rsp + 0x70 ]; load m64 x93 to register64
lea rsi, [ rsi + r10 ]; r8/64 + m8
mov r10, [ rsp + 0x60 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adcx r10, rsi
mov rbx, 0x0 ; moving imm to reg
adox rdx, rbx
movzx rsi, byte [ rsp + 0x58 ]; load byte memx133 to register64
dec rbx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox rsi, rbx; loading flag
adox r14, rcx
setc sil; spill CF x116 to reg (rsi)
clc;
movzx rbp, bpl
adcx rbp, rbx; loading flag
adcx r14, [ rsp + 0x20 ]
adox r15, rax
setc bpl; spill CF x159 to reg (rbp)
clc;
adcx r8, r12
mov r8, [ rsp + 0x68 ]; x181, copying x172 here, cause x172 is needed in a reg for other than x181, namely all: , x181--x182, size: 1
adcx r8, r14
adox rdx, r10
movzx r12, sil; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
mov rcx, 0x0 ; moving imm to reg
adox r12, rcx
setc al; spill CF x182 to reg (rax)
mov rsi, r8; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub rsi, 0x00000001
inc rbx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rcx; loading flag
adox r15, [ rsp + 0x18 ]
mov r10, [ rsp + 0x30 ]; x162, copying x153 here, cause x153 is needed in a reg for other than x162, namely all: , x162--x163, size: 1
adox r10, rdx
mov r14, [ rsp + 0x38 ]; x164, copying x155 here, cause x155 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adox r14, r12
seto bpl; spill OF x165 to reg (rbp)
inc rcx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rbx; loading flag
adox r15, [ rsp + 0xb0 ]
mov rax, [ rsp + 0xb8 ]; x185, copying x176 here, cause x176 is needed in a reg for other than x185, namely all: , x185--x186, size: 1
adox rax, r10
adox r13, r14
movzx rdx, bpl; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
adox rdx, rcx
mov r12, r15; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r10, 0xffffffff00000000 ; moving imm to reg
sbb r12, r10
mov rbp, rax; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov r14, 0xffffffffffffffff ; moving imm to reg
sbb rbp, r14
mov rcx, r13; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
mov rbx, 0xffffffff ; moving imm to reg
sbb rcx, rbx
sbb rdx, 0x00000000
cmovc rsi, r8; if CF, x200<- x181 (nzVar)
cmovc r12, r15; if CF, x201<- x183 (nzVar)
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x0 ], rsi; out1[0] = x200
cmovc rcx, r13; if CF, x203<- x187 (nzVar)
cmovc rbp, rax; if CF, x202<- x185 (nzVar)
mov [ r8 + 0x10 ], rbp; out1[2] = x202
mov [ r8 + 0x18 ], rcx; out1[3] = x203
mov [ r8 + 0x8 ], r12; out1[1] = x201
mov rbx, [ rsp + 0xc0 ]; restoring from stack
mov rbp, [ rsp + 0xc8 ]; restoring from stack
mov r12, [ rsp + 0xd0 ]; restoring from stack
mov r13, [ rsp + 0xd8 ]; restoring from stack
mov r14, [ rsp + 0xe0 ]; restoring from stack
mov r15, [ rsp + 0xe8 ]; restoring from stack
add rsp, 0xf0 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 94.01, best 66.28571428571429, lastGood 69.80530973451327
; seed 4097297752174669 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 866101 ms / 60000 runs=> 14.435016666666666ms/run
; Time spent for assembling and measureing (initial batch_size=112, initial num_batches=101): 151490 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.1749103164642461
; number reverted permutation/ tried permutation: 25292 / 29816 =84.827%
; number reverted decision/ tried decision: 21659 / 30185 =71.754%