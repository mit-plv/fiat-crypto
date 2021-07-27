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
mov rdx, [ rdx + 0x18 ]; saving arg2[3] in rdx.
mulx r11, rbx, rax; x6, x5<- x4 * arg2[3]
mov rdx, rax; x4 to rdx
mulx rax, rbp, [ r10 + 0x8 ]; x10, x9<- x4 * arg2[1]
mulx r12, r13, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
mulx rdx, r14, [ r10 + 0x0 ]; x12, x11<- x4 * arg2[0]
add rbp, rdx; could be done better, if r0 has been u8 as well
adcx r13, rax
adcx rbx, r12
adc r11, 0x0
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; x11 to rdx
mulx r14, rcx, r15; _, x20<- x11 * 0xffffffffffffffff
mov r14, rcx; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x24--x25, x22--x23, _--x34, x26--x27, size: 4
xor r8, r8
adox r14, rdx
mov r14, 0xffffffff00000000 ; moving imm to reg
mov rdx, r14; 0xffffffff00000000 to rdx
mulx r14, r9, rcx; x27, x26<- x20 * 0xffffffff00000000
adox r9, rbp
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r12, rdx; preserving value of 0xffffffff00000000 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r8, rax; x50, x49<- x1 * arg2[0]
adcx r8, r9
mov rdx, r15; 0xffffffffffffffff to rdx
mulx r15, r9, r8; _, x68<- x58 * 0xffffffffffffffff
mulx r15, r12, r9; x73, x72<- x68 * 0xffffffffffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r11; spilling x19 to mem
mulx rdi, r11, r9; x75, x74<- x68 * 0xffffffff00000000
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], rbx; spilling x17 to mem
mov [ rsp + 0x18 ], r11; spilling x74 to mem
mulx rbx, r11, r9; x71, x70<- x68 * 0xffffffff
mov rdx, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x20 ], rdx; spilling x3 to mem
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0x28 ], rbp; spilling x50 to mem
setc bpl; spill CF x59 to reg (rbp)
clc;
adcx r12, rdi
mov [ rsp + 0x30 ], r12; spilling x76 to mem
mulx rdi, r12, [ r10 + 0x0 ]; x99, x98<- x2 * arg2[0]
adcx r11, r15
mov r15, 0x0 ; moving imm to reg
adcx rbx, r15
mov [ rsp + 0x38 ], r12; spilling x98 to mem
mulx r15, r12, [ r10 + 0x8 ]; x97, x96<- x2 * arg2[1]
mov [ rsp + 0x40 ], rbx; spilling x80 to mem
mov [ rsp + 0x48 ], r11; spilling x78 to mem
mulx rbx, r11, [ r10 + 0x18 ]; x93, x92<- x2 * arg2[3]
clc;
adcx r12, rdi
mulx rdx, rdi, [ r10 + 0x10 ]; x95, x94<- x2 * arg2[2]
adcx rdi, r15
adcx r11, rdx
mov r15, 0x0 ; moving imm to reg
adcx rbx, r15
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x50 ], rbx; spilling x106 to mem
mulx r15, rbx, rax; x48, x47<- x1 * arg2[1]
mov [ rsp + 0x58 ], r11; spilling x104 to mem
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x20 to rdx
mov [ rsp + 0x60 ], rdi; spilling x102 to mem
mulx rcx, rdi, r11; x25, x24<- x20 * 0xffffffffffffffff
clc;
adcx rdi, r14
adox rdi, r13
seto r13b; spill OF x38 to reg (r13)
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x28 ]
setc r14b; spill CF x29 to reg (r14)
clc;
mov r11, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r11; loading flag
adcx rdi, rbx
setc bpl; spill CF x61 to reg (rbp)
clc;
adcx r9, r8
mov r9, [ rsp + 0x18 ]; x83, copying x74 here, cause x74 is needed in a reg for other than x83, namely all: , x83--x84, size: 1
adcx r9, rdi
mov r8, 0xffffffff ; moving imm to reg
mulx rdx, rbx, r8; x23, x22<- x20 * 0xffffffff
setc dil; spill CF x84 to reg (rdi)
clc;
movzx r14, r14b
adcx r14, r11; loading flag
adcx rcx, rbx
mov r14, 0x0 ; moving imm to reg
adcx rdx, r14
mov rbx, rdx; preserving value of x32 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mulx r14, r11, rax; x44, x43<- x1 * arg2[3]
clc;
mov r8, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r8; loading flag
adcx rcx, [ rsp + 0x10 ]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rax, r13, rax; x46, x45<- x1 * arg2[2]
mov r8, [ rsp + 0x8 ]; x41, copying x19 here, cause x19 is needed in a reg for other than x41, namely all: , x41--x42, size: 1
adcx r8, rbx
adox r13, r15
adox r11, rax
mov r15, 0x0 ; moving imm to reg
adox r14, r15
dec r15; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, r15; loading flag
adox rcx, r13
setc bpl; spill CF x42 to reg (rbp)
clc;
movzx rdi, dil
adcx rdi, r15; loading flag
adcx rcx, [ rsp + 0x30 ]
adox r11, r8
mov rdi, [ rsp + 0x48 ]; x87, copying x78 here, cause x78 is needed in a reg for other than x87, namely all: , x87--x88, size: 1
adcx rdi, r11
movzx rbx, bpl; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox rbx, r14
mov rax, [ rsp + 0x40 ]; x89, copying x80 here, cause x80 is needed in a reg for other than x89, namely all: , x89--x90, size: 1
adcx rax, rbx
seto bpl; spill OF x91 to reg (rbp)
adc bpl, 0x0
movzx rbp, bpl
adox r9, [ rsp + 0x38 ]
adox r12, rcx
mov r8, [ rsp + 0x60 ]; x111, copying x102 here, cause x102 is needed in a reg for other than x111, namely all: , x111--x112, size: 1
adox r8, rdi
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; x107 to rdx
mulx r9, r14, r13; _, x117<- x107 * 0xffffffffffffffff
mov r9, r14; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x123--x124, x119--x120, _--x131, x121--x122, size: 4
adcx r9, rdx
mov r9, [ rsp + 0x58 ]; x113, copying x104 here, cause x104 is needed in a reg for other than x113, namely all: , x113--x114, size: 1
adox r9, rax
mov rcx, 0xffffffff00000000 ; moving imm to reg
mov rdx, r14; x117 to rdx
mulx r14, r11, rcx; x124, x123<- x117 * 0xffffffff00000000
adcx r11, r12
mov rdi, rdx; preserving value of x117 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rax, [ rsp + 0x20 ]; x148, x147<- x3 * arg2[0]
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, r12, rdi; x122, x121<- x117 * 0xffffffffffffffff
seto r15b; spill OF x114 to reg (r15)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r14
seto r14b; spill OF x126 to reg (r14)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, r11
mov r11, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x68 ], rsi; spilling arg1 to mem
mulx rcx, rsi, [ rsp + 0x20 ]; x146, x145<- x3 * arg2[1]
adcx r12, r8
setc r8b; spill CF x135 to reg (r8)
clc;
adcx rsi, rbx
mov rdx, rax; x156 to rdx
mulx rax, rbx, r11; _, x166<- x156 * 0xffffffffffffffff
adox rsi, r12
mov rax, rbx; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , _--x180, x172--x173, x170--x171, x168--x169, size: 4
seto r12b; spill OF x159 to reg (r12)
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, rdx
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rax, r11, [ rsp + 0x20 ]; x144, x143<- x3 * arg2[2]
mov [ rsp + 0x70 ], rax; spilling x144 to mem
mov rax, 0xffffffff ; moving imm to reg
mov rdx, rax; 0xffffffff to rdx
mulx rdi, rax, rdi; x120, x119<- x117 * 0xffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov byte [ rsp + 0x78 ], bpl; spilling byte x91 to mem
mov byte [ rsp + 0x80 ], r15b; spilling byte x114 to mem
mulx rbp, r15, rbx; x173, x172<- x166 * 0xffffffff00000000
adcx r11, rcx
adox r15, rsi
setc cl; spill CF x152 to reg (rcx)
seto sil; spill OF x182 to reg (rsi)
mov rdx, r15; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x200, x190--x191, size: 2
sub rdx, 0x00000001
mov [ rsp + 0x88 ], rdx; spilling x190 to mem
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rdx; loading flag
adox r13, rax
mov r14, 0x0 ; moving imm to reg
adox rdi, r14
dec r14; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r8, r8b
adox r8, r14; loading flag
adox r9, r13
setc r8b; spill CF x191 to reg (r8)
clc;
movzx r12, r12b
adcx r12, r14; loading flag
adcx r9, r11
movzx r12, byte [ rsp + 0x78 ]; load byte memx91 to register64
setc al; spill CF x161 to reg (rax)
movzx r11, byte [ rsp + 0x80 ]; load byte memx114 to register64
clc;
adcx r11, r14; loading flag
adcx r12, [ rsp + 0x50 ]
adox rdi, r12
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r11, r13, [ rsp + 0x20 ]; x142, x141<- x3 * arg2[3]
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, r14, rbx; x171, x170<- x166 * 0xffffffffffffffff
seto dl; spill OF x140 to reg (rdx)
adc dl, 0x0
movzx rdx, dl
adox r14, rbp
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rbp; loading flag
adcx r13, [ rsp + 0x70 ]
seto cl; spill OF x175 to reg (rcx)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, rbp; loading flag
adox r9, r14
mov rsi, 0x0 ; moving imm to reg
adcx r11, rsi
seto r14b; spill OF x184 to reg (r14)
movzx rsi, r8b; x191, copying x191 here, cause x191 is needed in a reg for other than x191, namely all: , x192--x193, size: 1
add rsi, -0x1
mov r8, r9; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov rbp, 0xffffffff00000000 ; moving imm to reg
sbb r8, rbp
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rbp; loading flag
adox rdi, r13
movzx rax, dl; x164, copying x140 here, cause x140 is needed in a reg for other than x164, namely all: , x164--x165, size: 1
adox rax, r11
mov rdx, 0xffffffff ; moving imm to reg
mulx rbx, r13, rbx; x169, x168<- x166 * 0xffffffff
seto r11b; spill OF x165 to reg (r11)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbp; loading flag
adox r12, r13
mov rcx, 0x0 ; moving imm to reg
adox rbx, rcx
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r14, r14b
adox r14, rcx; loading flag
adox rdi, r12
adox rbx, rax
movzx rbp, r11b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
mov r14, 0x0 ; moving imm to reg
adox rbp, r14
mov r11, rdi; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov rax, 0xffffffffffffffff ; moving imm to reg
sbb r11, rax
mov r13, rbx; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
sbb r13, rdx
sbb rbp, 0x00000000
cmovc r13, rbx; if CF, x203<- x187 (nzVar)
cmovc r8, r9; if CF, x201<- x183 (nzVar)
mov rbp, [ rsp + 0x88 ]; x200, copying x190 here, cause x190 is needed in a reg for other than x200, namely all: , x200, size: 1
cmovc rbp, r15; if CF, x200<- x181 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x0 ], rbp; out1[0] = x200
cmovc r11, rdi; if CF, x202<- x185 (nzVar)
mov [ r15 + 0x18 ], r13; out1[3] = x203
mov [ r15 + 0x10 ], r11; out1[2] = x202
mov [ r15 + 0x8 ], r8; out1[1] = x201
mov rbx, [ rsp + 0x90 ]; restoring from stack
mov rbp, [ rsp + 0x98 ]; restoring from stack
mov r12, [ rsp + 0xa0 ]; restoring from stack
mov r13, [ rsp + 0xa8 ]; restoring from stack
mov r14, [ rsp + 0xb0 ]; restoring from stack
mov r15, [ rsp + 0xb8 ]; restoring from stack
add rsp, 0xc0 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 97.06, best 74.72477064220183, lastGood 75.4862385321101
; seed 3485352012649499 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1186328 ms / 60000 runs=> 19.772133333333333ms/run
; Time spent for assembling and measureing (initial batch_size=109, initial num_batches=101): 204590 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.1724565212993371
; number reverted permutation/ tried permutation: 24537 / 29947 =81.935%
; number reverted decision/ tried decision: 22323 / 30054 =74.276%