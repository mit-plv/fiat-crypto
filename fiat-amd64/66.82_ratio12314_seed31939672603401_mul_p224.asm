SECTION .text
	GLOBAL mul_p224
mul_p224:
sub rsp, 0xc0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x90 ], rbx; saving to stack
mov [ rsp + 0x98 ], rbp; saving to stack
mov [ rsp + 0xa0 ], r12; saving to stack
mov [ rsp + 0xa8 ], r13; saving to stack
mov [ rsp + 0xb0 ], r14; saving to stack
mov [ rsp + 0xb8 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x12, x11<- x4 * arg2[0]
mov rdx, rax; x4 to rdx
mulx rax, rbp, [ r10 + 0x8 ]; x10, x9<- x4 * arg2[1]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mulx r13, r14, rbx; _, x20<- x11 * 0xffffffffffffffff
mov r13, r14; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , _--x34, x22--x23, x26--x27, x24--x25, size: 4
test al, al
adox r13, rbx
adcx rbp, r11
xchg rdx, r12; x4, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r13, r15, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
mov rcx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; 0xffffffff00000000, swapping with x4, which is currently in rdx
mulx r8, r9, r14; x27, x26<- x20 * 0xffffffff00000000
adox r9, rbp
mov r11, [ rsi + 0x8 ]; load m64 x1 to register64
xchg rdx, r11; x1, swapping with 0xffffffff00000000, which is currently in rdx
mulx rbx, rbp, [ r10 + 0x0 ]; x50, x49<- x1 * arg2[0]
adcx r15, rax
setc al; spill CF x16 to reg (rax)
clc;
adcx rbp, r9
xchg rdx, r12; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r9, r11, rbp; _, x68<- x58 * 0xffffffffffffffff
mov r9, 0xffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r14; x23, x22<- x20 * 0xffffffff
xchg rdx, r12; x1, swapping with 0xffffffff, which is currently in rdx
mov [ rsp + 0x8 ], r9; spilling x23 to mem
mulx r12, r9, [ r10 + 0x8 ]; x48, x47<- x1 * arg2[1]
mov [ rsp + 0x10 ], r12; spilling x48 to mem
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x20, swapping with x1, which is currently in rdx
mov [ rsp + 0x18 ], r13; spilling x8 to mem
mulx rdx, r13, r12; x25, x24<- x20 * 0xffffffffffffffff
xchg rdx, rcx; x4, swapping with x25, which is currently in rdx
mulx rdx, r12, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
mov [ rsp + 0x20 ], rdx; spilling x6 to mem
mov rdx, r11; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , x72--x73, _--x82, x74--x75, x70--x71, size: 4
mov [ rsp + 0x28 ], r12; spilling x5 to mem
setc r12b; spill CF x59 to reg (r12)
clc;
adcx rdx, rbp
setc bpl; spill CF x82 to reg (rbp)
clc;
adcx r9, rbx
setc bl; spill CF x52 to reg (rbx)
clc;
adcx r13, r8
mov r8, 0xffffffff ; moving imm to reg
mov rdx, r11; x68 to rdx
mov byte [ rsp + 0x30 ], bl; spilling byte x52 to mem
mulx r11, rbx, r8; x71, x70<- x68 * 0xffffffff
adcx rdi, rcx
adox r13, r15
mov r15, 0xffffffff00000000 ; moving imm to reg
mulx rcx, r8, r15; x75, x74<- x68 * 0xffffffff00000000
setc r15b; spill CF x31 to reg (r15)
clc;
mov [ rsp + 0x38 ], rsi; spilling arg1 to mem
mov rsi, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rsi; loading flag
adcx r13, r9
setc r12b; spill CF x61 to reg (r12)
clc;
movzx rbp, bpl
adcx rbp, rsi; loading flag
adcx r13, r8
mov rbp, rdx; preserving value of x68 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx r9, r8, r14; x44, x43<- x1 * arg2[3]
mov rsi, [ rsp + 0x28 ]; load m64 x5 to register64
mov [ rsp + 0x40 ], r13; spilling x83 to mem
setc r13b; spill CF x84 to reg (r13)
clc;
mov [ rsp + 0x48 ], r9; spilling x44 to mem
mov r9, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r9; loading flag
adcx rsi, [ rsp + 0x18 ]
adox rdi, rsi
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; x68 to rdx
mulx rdx, rbp, rax; x73, x72<- x68 * 0xffffffffffffffff
movzx rsi, r15b; x32, copying x31 here, cause x31 is needed in a reg for other than x32, namely all: , x32, size: 1
mov r9, [ rsp + 0x8 ]; load m64 x23 to register64
lea rsi, [ rsi + r9 ]; r8/64 + m8
mov r9, [ rsp + 0x20 ]; x19, copying x6 here, cause x6 is needed in a reg for other than x19, namely all: , x19, size: 1
mov r15, 0x0 ; moving imm to reg
adcx r9, r15
adox rsi, r9
xchg rdx, r14; x1, swapping with x73, which is currently in rdx
mulx rdx, r9, [ r10 + 0x10 ]; x46, x45<- x1 * arg2[2]
movzx r15, byte [ rsp + 0x30 ]; load byte memx52 to register64
clc;
mov rax, -0x1 ; moving imm to reg
adcx r15, rax; loading flag
adcx r9, [ rsp + 0x10 ]
setc r15b; spill CF x54 to reg (r15)
clc;
movzx r12, r12b
adcx r12, rax; loading flag
adcx rdi, r9
setc r12b; spill CF x63 to reg (r12)
clc;
adcx rbp, rcx
adcx rbx, r14
seto cl; spill OF x42 to reg (rcx)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox rdi, rbp
adcx r11, rax
clc;
movzx r15, r15b
adcx r15, r14; loading flag
adcx rdx, r8
mov r13, [ rsp + 0x38 ]; load m64 arg1 to register64
mov r8, [ r13 + 0x10 ]; load m64 x2 to register64
mov r9, [ rsp + 0x48 ]; x57, copying x44 here, cause x44 is needed in a reg for other than x57, namely all: , x57, size: 1
adcx r9, rax
mov r15, [ r13 + 0x18 ]; load m64 x3 to register64
xchg rdx, r8; x2, swapping with x55, which is currently in rdx
mulx rbp, rax, [ r10 + 0x0 ]; x99, x98<- x2 * arg2[0]
mov [ rsp + 0x50 ], r15; spilling x3 to mem
mulx r14, r15, [ r10 + 0x10 ]; x95, x94<- x2 * arg2[2]
clc;
mov [ rsp + 0x58 ], rdi; spilling x85 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rdi; loading flag
adcx rsi, r8
adox rbx, rsi
movzx r12, cl; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adcx r12, r9
mulx rcx, r8, [ r10 + 0x8 ]; x97, x96<- x2 * arg2[1]
mulx rdx, r9, [ r10 + 0x18 ]; x93, x92<- x2 * arg2[3]
adox r11, r12
seto sil; spill OF x90 to reg (rsi)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rbp
movzx rbp, sil; x91, copying x90 here, cause x90 is needed in a reg for other than x91, namely all: , x91, size: 1
adcx rbp, rdi
clc;
adcx rax, [ rsp + 0x40 ]
adox r15, rcx
adox r9, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x107, swapping with x93, which is currently in rdx
mulx r12, rcx, r14; _, x117<- x107 * 0xffffffffffffffff
xchg rdx, r14; 0xffffffffffffffff, swapping with x107, which is currently in rdx
mulx r12, rsi, rcx; x122, x121<- x117 * 0xffffffffffffffff
adox rax, rdi
mov rdi, 0xffffffff00000000 ; moving imm to reg
xchg rdx, rcx; x117, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x60 ], rax; spilling x106 to mem
mulx rcx, rax, rdi; x124, x123<- x117 * 0xffffffff00000000
mov rdi, [ rsp + 0x58 ]; x109, copying x85 here, cause x85 is needed in a reg for other than x109, namely all: , x109--x110, size: 1
adcx rdi, r8
mov r8, rdx; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , _--x131, x119--x120, size: 2
mov [ rsp + 0x68 ], rbp; spilling x91 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r14
mov r8, 0xffffffff ; moving imm to reg
mulx rdx, r14, r8; x120, x119<- x117 * 0xffffffff
adcx r15, rbx
adox rax, rdi
setc bl; spill CF x112 to reg (rbx)
clc;
adcx rsi, rcx
mov rcx, rdx; preserving value of x120 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rdi, rbp, [ rsp + 0x50 ]; x148, x147<- x3 * arg2[0]
adcx r14, r12
mov r12, 0x0 ; moving imm to reg
adcx rcx, r12
clc;
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r12; loading flag
adcx r11, r9
adox rsi, r15
mov rdx, [ rsp + 0x50 ]; x3 to rdx
mulx r9, rbx, [ r10 + 0x8 ]; x146, x145<- x3 * arg2[1]
adox r14, r11
mov r15, [ rsp + 0x60 ]; load m64 x106 to register64
mov r11, [ rsp + 0x68 ]; x115, copying x91 here, cause x91 is needed in a reg for other than x115, namely all: , x115--x116, size: 1
adcx r11, r15
setc r15b; spill CF x116 to reg (r15)
clc;
adcx rbx, rdi
mulx rdi, r12, [ r10 + 0x10 ]; x144, x143<- x3 * arg2[2]
adox rcx, r11
mulx rdx, r11, [ r10 + 0x18 ]; x142, x141<- x3 * arg2[3]
movzx r8, r15b; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
mov [ rsp + 0x70 ], rcx; spilling x138 to mem
mov rcx, 0x0 ; moving imm to reg
adox r8, rcx
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, rax
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; 0xffffffffffffffff, swapping with x142, which is currently in rdx
mulx rcx, r15, rbp; _, x166<- x156 * 0xffffffffffffffff
adox rbx, rsi
adcx r12, r9
mov rcx, r15; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , x168--x169, _--x180, x172--x173, x170--x171, size: 4
setc sil; spill CF x152 to reg (rsi)
clc;
adcx rcx, rbp
mov rcx, 0xffffffff00000000 ; moving imm to reg
xchg rdx, r15; x166, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r9, rbp, rcx; x173, x172<- x166 * 0xffffffff00000000
adcx rbp, rbx
adox r12, r14
mulx r14, rbx, r15; x171, x170<- x166 * 0xffffffffffffffff
mov rcx, 0xffffffff ; moving imm to reg
mulx rdx, r15, rcx; x169, x168<- x166 * 0xffffffff
setc cl; spill CF x182 to reg (rcx)
mov [ rsp + 0x78 ], rdx; spilling x169 to mem
seto dl; spill OF x161 to reg (rdx)
mov [ rsp + 0x80 ], r12; spilling x160 to mem
mov r12, rbp; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub r12, 0x00000001
mov [ rsp + 0x88 ], r12; spilling x190 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r9
adox r15, r14
setc r9b; spill CF x191 to reg (r9)
clc;
movzx rsi, sil
adcx rsi, r12; loading flag
adcx rdi, r11
mov r11, 0x0 ; moving imm to reg
adcx rax, r11
clc;
movzx rdx, dl
adcx rdx, r12; loading flag
adcx rdi, [ rsp + 0x70 ]
adcx rax, r8
setc r8b; spill CF x165 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, r12; loading flag
adcx rbx, [ rsp + 0x80 ]
adcx r15, rdi
mov rsi, [ rsp + 0x78 ]; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178, size: 1
adox rsi, r11
adcx rsi, rax
movzx rcx, r8b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
adc rcx, 0x0
movzx rdx, r9b; x191, copying x191 here, cause x191 is needed in a reg for other than x191, namely all: , x192--x193, size: 1
add rdx, -0x1
mov r9, rbx; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r14, 0xffffffff00000000 ; moving imm to reg
sbb r9, r14
mov rdi, r15; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb rdi, r8
mov rax, rsi; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x196--x197, x203, size: 2
mov r11, 0xffffffff ; moving imm to reg
sbb rax, r11
sbb rcx, 0x00000000
cmovc r9, rbx; if CF, x201<- x183 (nzVar)
mov rcx, [ rsp + 0x88 ]; x200, copying x190 here, cause x190 is needed in a reg for other than x200, namely all: , x200, size: 1
cmovc rcx, rbp; if CF, x200<- x181 (nzVar)
cmovc rdi, r15; if CF, x202<- x185 (nzVar)
cmovc rax, rsi; if CF, x203<- x187 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x10 ], rdi; out1[2] = x202
mov [ rbp + 0x8 ], r9; out1[1] = x201
mov [ rbp + 0x18 ], rax; out1[3] = x203
mov [ rbp + 0x0 ], rcx; out1[0] = x200
mov rbx, [ rsp + 0x90 ]; restoring from stack
mov rbp, [ rsp + 0x98 ]; restoring from stack
mov r12, [ rsp + 0xa0 ]; restoring from stack
mov r13, [ rsp + 0xa8 ]; restoring from stack
mov r14, [ rsp + 0xb0 ]; restoring from stack
mov r15, [ rsp + 0xb8 ]; restoring from stack
add rsp, 0xc0 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 86.83, best 65.55, lastGood 66.81666666666666
; seed 31939672603401 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 642005 ms / 60000 runs=> 10.700083333333334ms/run
; Time spent for assembling and measureing (initial batch_size=119, initial num_batches=101): 131960 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.20554357053293978
; number reverted permutation/ tried permutation: 25098 / 29885 =83.982%
; number reverted decision/ tried decision: 21881 / 30116 =72.656%