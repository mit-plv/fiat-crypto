SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0xd0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xa0 ], rbx; saving to stack
mov [ rsp + 0xa8 ], rbp; saving to stack
mov [ rsp + 0xb0 ], r12; saving to stack
mov [ rsp + 0xb8 ], r13; saving to stack
mov [ rsp + 0xc0 ], r14; saving to stack
mov [ rsp + 0xc8 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
mov r11, [ rsi + 0x0 ]; load m64 x4 to register64
mov rbx, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx rbp, r12, r11; x10, x9<- x4 * arg2[1]
mov rdx, r10; x2 to rdx
mulx r10, r13, [ rbx + 0x18 ]; x85, x84<- x2 * arg2[3]
mulx r14, r15, [ rbx + 0x10 ]; x87, x86<- x2 * arg2[2]
mulx rcx, r8, [ rbx + 0x8 ]; x89, x88<- x2 * arg2[1]
mulx rdx, r9, [ rbx + 0x0 ]; x91, x90<- x2 * arg2[0]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
xor rdi, rdi
adox r8, rdx
adox r15, rcx
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mulx rcx, rdi, r11; x12, x11<- x4 * arg2[0]
adox r13, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; 0xffffffffffffffff to rdx
mov [ rsp + 0x8 ], r13; spilling x96 to mem
mulx r14, r13, rdi; x25, x24<- x11 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
adox r10, rdx
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], r10; spilling x98 to mem
mov [ rsp + 0x18 ], r15; spilling x94 to mem
mulx r10, r15, rdi; x23, x22<- x11 * 0xffffffff
adcx r15, r14
adc r10, 0x0
mov r14, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ rbx + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x20 ], rsi; spilling arg1 to mem
mov [ rsp + 0x28 ], r8; spilling x92 to mem
mulx rsi, r8, rax; x44, x43<- x1 * arg2[1]
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x30 ], rsi; spilling x44 to mem
mulx r14, rsi, rax; x46, x45<- x1 * arg2[0]
test al, al
adox r13, rdi
mov rdx, r11; x4 to rdx
mulx r11, r13, [ rbx + 0x10 ]; x8, x7<- x4 * arg2[2]
adcx r12, rcx
adox r15, r12
adcx r13, rbp
setc bpl; spill CF x16 to reg (rbp)
clc;
adcx r8, r14
setc cl; spill CF x48 to reg (rcx)
clc;
adcx rsi, r15
mov r14, 0xffffffff ; moving imm to reg
xchg rdx, rsi; x54, swapping with x4, which is currently in rdx
mulx r12, r15, r14; x67, x66<- x54 * 0xffffffff
mov r14, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x38 ], cl; spilling byte x48 to mem
mov [ rsp + 0x40 ], r11; spilling x8 to mem
mulx rcx, r11, r14; x69, x68<- x54 * 0xffffffffffffffff
adox r10, r13
adcx r8, r10
setc r13b; spill CF x57 to reg (r13)
clc;
adcx r15, rcx
setc cl; spill CF x71 to reg (rcx)
clc;
adcx r11, rdx
adcx r15, r8
movzx r11, cl; x72, copying x71 here, cause x71 is needed in a reg for other than x72, namely all: , x72, size: 1
lea r11, [ r11 + r12 ]
mov r12, rdx; preserving value of x54 into a new reg
mov rdx, [ rbx + 0x10 ]; saving arg2[2] in rdx.
mulx r10, r8, rax; x42, x41<- x1 * arg2[2]
setc cl; spill CF x76 to reg (rcx)
clc;
adcx r9, r15
mov rdx, r9; x99 to rdx
mulx r9, r15, r14; x114, x113<- x99 * 0xffffffffffffffff
setc r14b; spill CF x100 to reg (r14)
clc;
adcx r15, rdx
mov r15, rdx; preserving value of x99 into a new reg
mov rdx, [ rbx + 0x18 ]; saving arg2[3] in rdx.
mov byte [ rsp + 0x48 ], r14b; spilling byte x100 to mem
mulx rsi, r14, rsi; x6, x5<- x4 * arg2[3]
mov [ rsp + 0x50 ], r11; spilling x72 to mem
mov r11, 0xffffffff00000001 ; moving imm to reg
mov rdx, r11; 0xffffffff00000001 to rdx
mulx rdi, r11, rdi; x21, x20<- x11 * 0xffffffff00000001
setc dl; spill CF x119 to reg (rdx)
clc;
mov byte [ rsp + 0x58 ], cl; spilling byte x76 to mem
mov rcx, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx r14, [ rsp + 0x40 ]
setc bpl; spill CF x18 to reg (rbp)
movzx rcx, byte [ rsp + 0x38 ]; load byte memx48 to register64
clc;
mov byte [ rsp + 0x60 ], dl; spilling byte x119 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rcx, rdx; loading flag
adcx r8, [ rsp + 0x30 ]
movzx rcx, bpl; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
lea rcx, [ rcx + rsi ]
adox r11, r14
adox rdi, rcx
mov rsi, 0xffffffff ; moving imm to reg
mov rdx, rsi; 0xffffffff to rdx
mulx r14, rbp, r15; x112, x111<- x99 * 0xffffffff
seto cl; spill OF x38 to reg (rcx)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r9
seto r9b; spill OF x116 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdx; loading flag
adox r11, r8
mov rdx, rax; x1 to rdx
mulx rdx, rax, [ rbx + 0x18 ]; x40, x39<- x1 * arg2[3]
adcx rax, r10
adox rax, rdi
setc r13b; spill CF x52 to reg (r13)
movzx r10, byte [ rsp + 0x58 ]; load byte memx76 to register64
clc;
mov r8, -0x1 ; moving imm to reg
adcx r10, r8; loading flag
adcx r11, [ rsp + 0x50 ]
setc r10b; spill CF x78 to reg (r10)
movzx rdi, byte [ rsp + 0x48 ]; load byte memx100 to register64
clc;
adcx rdi, r8; loading flag
adcx r11, [ rsp + 0x28 ]
mov rdi, [ rsp + 0x20 ]; load m64 arg1 to register64
mov r8, [ rdi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x68 ], r8; spilling x3 to mem
movzx r8, r9b; x117, copying x116 here, cause x116 is needed in a reg for other than x117, namely all: , x117, size: 1
lea r8, [ r8 + r14 ]
setc r14b; spill CF x102 to reg (r14)
movzx r9, byte [ rsp + 0x60 ]; load byte memx119 to register64
clc;
mov [ rsp + 0x70 ], r8; spilling x117 to mem
mov r8, -0x1 ; moving imm to reg
adcx r9, r8; loading flag
adcx r11, rbp
movzx r9, r13b; x53, copying x52 here, cause x52 is needed in a reg for other than x53, namely all: , x53, size: 1
lea r9, [ r9 + rdx ]
movzx rbp, cl; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox rbp, r9
mov rcx, 0xffffffff00000001 ; moving imm to reg
mov rdx, rcx; 0xffffffff00000001 to rdx
mulx r12, rcx, r12; x65, x64<- x54 * 0xffffffff00000001
seto r13b; spill OF x63 to reg (r13)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r9; loading flag
adox rax, rcx
mulx r15, r10, r15; x110, x109<- x99 * 0xffffffff00000001
mov rcx, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ rbx + 0x8 ]; saving arg2[1] in rdx.
mulx r8, r9, [ rsp + 0x68 ]; x134, x133<- x3 * arg2[1]
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x78 ], r8; spilling x134 to mem
mulx rcx, r8, [ rsp + 0x68 ]; x136, x135<- x3 * arg2[0]
adox r12, rbp
movzx rbp, r13b; x83, copying x63 here, cause x63 is needed in a reg for other than x83, namely all: , x83, size: 1
mov [ rsp + 0x80 ], r9; spilling x133 to mem
mov r9, 0x0 ; moving imm to reg
adox rbp, r9
dec r9; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r14, r14b
adox r14, r9; loading flag
adox rax, [ rsp + 0x18 ]
mov r14, [ rsp + 0x8 ]; x105, copying x96 here, cause x96 is needed in a reg for other than x105, namely all: , x105--x106, size: 1
adox r14, r12
mov r13, [ rsp + 0x70 ]; x122, copying x117 here, cause x117 is needed in a reg for other than x122, namely all: , x122--x123, size: 1
adcx r13, rax
mov r12, [ rsp + 0x10 ]; x107, copying x98 here, cause x98 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adox r12, rbp
adcx r10, r14
adcx r15, r12
seto bpl; spill OF x128 to reg (rbp)
adc bpl, 0x0
movzx rbp, bpl
adox r8, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x144 to rdx
mulx r8, rax, r11; x159, x158<- x144 * 0xffffffffffffffff
mov r14, 0xffffffff ; moving imm to reg
mulx r12, r9, r14; x157, x156<- x144 * 0xffffffff
adcx r9, r8
mov r8, 0x0 ; moving imm to reg
adcx r12, r8
clc;
adcx rcx, [ rsp + 0x80 ]
setc r14b; spill CF x138 to reg (r14)
clc;
adcx rax, rdx
adox rcx, r13
adcx r9, rcx
mov rax, rdx; preserving value of x144 into a new reg
mov rdx, [ rbx + 0x10 ]; saving arg2[2] in rdx.
mulx r13, rcx, [ rsp + 0x68 ]; x132, x131<- x3 * arg2[2]
mov byte [ rsp + 0x88 ], bpl; spilling byte x128 to mem
setc bpl; spill CF x166 to reg (rbp)
mov [ rsp + 0x90 ], r15; spilling x126 to mem
seto r15b; spill OF x147 to reg (r15)
mov [ rsp + 0x98 ], r12; spilling x162 to mem
mov r12, r9; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
sub r12, r11
dec r8; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r14, r14b
adox r14, r8; loading flag
adox rcx, [ rsp + 0x78 ]
mov rdx, [ rbx + 0x18 ]; arg2[3] to rdx
mulx r14, r8, [ rsp + 0x68 ]; x130, x129<- x3 * arg2[3]
mov r11, 0xffffffff00000001 ; moving imm to reg
mov rdx, rax; x144 to rdx
mulx rdx, rax, r11; x155, x154<- x144 * 0xffffffff00000001
adox r8, r13
mov r13, 0x0 ; moving imm to reg
adox r14, r13
dec r13; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r15, r15b
adox r15, r13; loading flag
adox r10, rcx
seto r15b; spill OF x149 to reg (r15)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rcx; loading flag
adox r10, [ rsp + 0x98 ]
seto bpl; spill OF x168 to reg (rbp)
mov r13, r10; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov rcx, 0xffffffff ; moving imm to reg
sbb r13, rcx
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rcx; loading flag
adox r8, [ rsp + 0x90 ]
movzx r15, byte [ rsp + 0x88 ]; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox r15, r14
seto r14b; spill OF x153 to reg (r14)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rcx; loading flag
adox r8, rax
adox rdx, r15
movzx rax, r14b; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
mov rbp, 0x0 ; moving imm to reg
adox rax, rbp
mov r14, r8; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178--x179, x186, size: 2
sbb r14, 0x00000000
mov r15, rdx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x180--x181, x187, size: 2
sbb r15, r11
sbb rax, 0x00000000
cmovc r13, r10; if CF, x185<- x167 (nzVar)
cmovc r14, r8; if CF, x186<- x169 (nzVar)
mov rax, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rax + 0x10 ], r14; out1[2] = x186
mov [ rax + 0x8 ], r13; out1[1] = x185
cmovc r12, r9; if CF, x184<- x165 (nzVar)
cmovc r15, rdx; if CF, x187<- x171 (nzVar)
mov [ rax + 0x18 ], r15; out1[3] = x187
mov [ rax + 0x0 ], r12; out1[0] = x184
mov rbx, [ rsp + 0xa0 ]; restoring from stack
mov rbp, [ rsp + 0xa8 ]; restoring from stack
mov r12, [ rsp + 0xb0 ]; restoring from stack
mov r13, [ rsp + 0xb8 ]; restoring from stack
mov r14, [ rsp + 0xc0 ]; restoring from stack
mov r15, [ rsp + 0xc8 ]; restoring from stack
add rsp, 0xd0 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 94.45, best 70.48598130841121, lastGood 73.26415094339623
; seed 1973146713415797 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1067361 ms / 60000 runs=> 17.78935ms/run
; Time spent for assembling and measureing (initial batch_size=106, initial num_batches=101): 231808 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.21717863028534862
; number reverted permutation/ tried permutation: 23924 / 29982 =79.795%
; number reverted decision/ tried decision: 22854 / 30019 =76.132%