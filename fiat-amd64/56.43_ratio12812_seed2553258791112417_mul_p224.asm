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
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rbp, r12, rax; x10, x9<- x4 * arg2[1]
mov r13, [ rsi + 0x8 ]; load m64 x1 to register64
xor r14, r14
adox r12, r11
mov r15, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; x11 to rdx
mulx rbx, rcx, r15; _, x20<- x11 * 0xffffffffffffffff
mov rbx, rdx; preserving value of x11 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, r9, r13; x50, x49<- x1 * arg2[0]
mov r11, 0xffffffff00000000 ; moving imm to reg
mov rdx, r11; 0xffffffff00000000 to rdx
mulx r11, r14, rcx; x27, x26<- x20 * 0xffffffff00000000
mov rdx, rcx; _, copying x20 here, cause x20 is needed in a reg for other than _, namely all: , x22--x23, _--x34, x24--x25, size: 3
adcx rdx, rbx
adcx r14, r12
setc bl; spill CF x36 to reg (rbx)
clc;
adcx r9, r14
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r12, r14, rax; x8, x7<- x4 * arg2[2]
adox r14, rbp
mov rdx, r15; 0xffffffffffffffff to rdx
mulx r15, rbp, r9; _, x68<- x58 * 0xffffffffffffffff
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r15, rdi, rcx; x25, x24<- x20 * 0xffffffffffffffff
mov rdx, 0xffffffff00000000 ; moving imm to reg
mov [ rsp + 0x8 ], rsi; spilling arg1 to mem
mov [ rsp + 0x10 ], r14; spilling x15 to mem
mulx rsi, r14, rbp; x75, x74<- x68 * 0xffffffff00000000
mov rdx, rbp; _, copying x68 here, cause x68 is needed in a reg for other than _, namely all: , _--x82, x70--x71, x72--x73, size: 3
mov [ rsp + 0x18 ], rsi; spilling x75 to mem
setc sil; spill CF x59 to reg (rsi)
clc;
adcx rdx, r9
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rax, r9, rax; x6, x5<- x4 * arg2[3]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x20 ], r14; spilling x74 to mem
mov byte [ rsp + 0x28 ], sil; spilling byte x59 to mem
mulx r14, rsi, r13; x48, x47<- x1 * arg2[1]
adox r9, r12
mov r12, 0xffffffff ; moving imm to reg
mov rdx, r12; 0xffffffff to rdx
mulx rcx, r12, rcx; x23, x22<- x20 * 0xffffffff
setc dl; spill CF x82 to reg (rdx)
clc;
adcx rsi, r8
setc r8b; spill CF x52 to reg (r8)
clc;
adcx rdi, r11
mov r11, 0x0 ; moving imm to reg
adox rax, r11
adcx r12, r15
adc rcx, 0x0
add bl, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto bl; since that has deps, resore it whereever it was
adox rdi, [ rsp + 0x10 ]
movzx rbx, byte [ rsp + 0x28 ]; load byte memx59 to register64
mov r15, -0x1 ; moving imm to reg
adcx rbx, r15; loading flag
adcx rdi, rsi
setc bl; spill CF x61 to reg (rbx)
clc;
movzx rdx, dl
adcx rdx, r15; loading flag
adcx rdi, [ rsp + 0x20 ]
adox r12, r9
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r9, rsi, r13; x46, x45<- x1 * arg2[2]
mov r11, 0xffffffff ; moving imm to reg
mov rdx, r11; 0xffffffff to rdx
mulx r11, r15, rbp; x71, x70<- x68 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x30 ], rdi; spilling x83 to mem
mulx rbp, rdi, rbp; x73, x72<- x68 * 0xffffffffffffffff
adox rcx, rax
setc al; spill CF x84 to reg (rax)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r14, rsi
seto r8b; spill OF x42 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0x18 ]
seto sil; spill OF x77 to reg (rsi)
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbx, bl
adox rbx, rdx; loading flag
adox r12, r14
mov rdx, r13; x1 to rdx
mulx rdx, r13, [ r10 + 0x18 ]; x44, x43<- x1 * arg2[3]
adcx r13, r9
adox r13, rcx
mov rbx, [ rsp + 0x8 ]; load m64 arg1 to register64
mov r9, [ rbx + 0x10 ]; load m64 x2 to register64
mov rcx, 0x0 ; moving imm to reg
adcx rdx, rcx
clc;
mov r14, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r14; loading flag
adcx r12, rdi
movzx rax, r8b; x66, copying x42 here, cause x42 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox rax, rdx
seto r8b; spill OF x67 to reg (r8)
inc r14; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, rcx; loading flag
adox rbp, r15
adcx rbp, r13
adox r11, r14
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r15, rdi, r9; x93, x92<- x2 * arg2[3]
mov rdx, r9; x2 to rdx
mulx r9, rsi, [ r10 + 0x10 ]; x95, x94<- x2 * arg2[2]
adcx r11, rax
mov r13, [ rbx + 0x18 ]; load m64 x3 to register64
movzx rax, r8b; x91, copying x67 here, cause x67 is needed in a reg for other than x91, namely all: , x91, size: 1
adc rax, 0x0
mulx r8, r14, [ r10 + 0x8 ]; x97, x96<- x2 * arg2[1]
mulx rdx, rcx, [ r10 + 0x0 ]; x99, x98<- x2 * arg2[0]
mov [ rsp + 0x38 ], rax; spilling x91 to mem
xor rax, rax
adox rcx, [ rsp + 0x30 ]
adcx r14, rdx
adcx rsi, r8
adox r14, r12
adcx rdi, r9
adcx r15, rax
adox rsi, rbp
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r12, rbp, r13; x148, x147<- x3 * arg2[0]
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, rcx; x107 to rdx
mulx rcx, r8, r9; _, x117<- x107 * 0xffffffffffffffff
mov rcx, r8; _, copying x117 here, cause x117 is needed in a reg for other than _, namely all: , x123--x124, x119--x120, x121--x122, _--x131, size: 4
clc;
adcx rcx, rdx
mov rcx, 0xffffffff00000000 ; moving imm to reg
mov rdx, r8; x117 to rdx
mulx r8, rax, rcx; x124, x123<- x117 * 0xffffffff00000000
mov [ rsp + 0x40 ], r15; spilling x106 to mem
mulx rcx, r15, r9; x122, x121<- x117 * 0xffffffffffffffff
adcx rax, r14
setc r14b; spill CF x133 to reg (r14)
clc;
adcx rbp, rax
mov rax, rdx; preserving value of x117 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x48 ], rcx; spilling x122 to mem
mulx r9, rcx, r13; x146, x145<- x3 * arg2[1]
mov [ rsp + 0x50 ], r9; spilling x146 to mem
setc r9b; spill CF x157 to reg (r9)
clc;
adcx rcx, r12
setc r12b; spill CF x150 to reg (r12)
clc;
adcx r15, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mov byte [ rsp + 0x58 ], r12b; spilling byte x150 to mem
mulx r8, r12, rbp; _, x166<- x156 * 0xffffffffffffffff
setc r8b; spill CF x126 to reg (r8)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rdx; loading flag
adcx rsi, r15
setc r14b; spill CF x135 to reg (r14)
clc;
movzx r9, r9b
adcx r9, rdx; loading flag
adcx rsi, rcx
mov r9, 0xffffffff00000000 ; moving imm to reg
mov rdx, r9; 0xffffffff00000000 to rdx
mulx r9, rcx, r12; x173, x172<- x166 * 0xffffffff00000000
adox rdi, r11
mov r11, r12; _, copying x166 here, cause x166 is needed in a reg for other than _, namely all: , x168--x169, x170--x171, _--x180, size: 3
setc r15b; spill CF x159 to reg (r15)
clc;
adcx r11, rbp
adcx rcx, rsi
setc r11b; spill CF x182 to reg (r11)
seto bpl; spill OF x114 to reg (rbp)
mov rsi, rcx; x190, copying x181 here, cause x181 is needed in a reg for other than x190, namely all: , x190--x191, x200, size: 2
sub rsi, 0x00000001
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x60 ], rsi; spilling x190 to mem
mulx rax, rsi, rax; x120, x119<- x117 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x68 ], r11b; spilling byte x182 to mem
mov byte [ rsp + 0x70 ], r15b; spilling byte x159 to mem
mulx r11, r15, r12; x171, x170<- x166 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, rdx; loading flag
adox rsi, [ rsp + 0x48 ]
mov rdx, r13; x3 to rdx
mulx r13, r8, [ r10 + 0x10 ]; x144, x143<- x3 * arg2[2]
mov [ rsp + 0x78 ], r11; spilling x171 to mem
setc r11b; spill CF x191 to reg (r11)
clc;
adcx r15, r9
setc r9b; spill CF x175 to reg (r9)
mov byte [ rsp + 0x80 ], r11b; spilling byte x191 to mem
movzx r11, byte [ rsp + 0x58 ]; load byte memx150 to register64
clc;
mov [ rsp + 0x88 ], r15; spilling x174 to mem
mov r15, -0x1 ; moving imm to reg
adcx r11, r15; loading flag
adcx r8, [ rsp + 0x50 ]
mov r11, 0x0 ; moving imm to reg
adox rax, r11
mulx rdx, r11, [ r10 + 0x18 ]; x142, x141<- x3 * arg2[3]
adcx r11, r13
adc rdx, 0x0
add r14b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r14b; since that has deps, resore it whereever it was
adox rdi, rsi
mov r14, [ rsp + 0x38 ]; load m64 x91 to register64
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx r14, [ rsp + 0x40 ]
adox rax, r14
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, r12; x166, swapping with x155, which is currently in rdx
mulx rdx, rsi, rbp; x169, x168<- x166 * 0xffffffff
setc r13b; spill CF x116 to reg (r13)
movzx r14, byte [ rsp + 0x70 ]; load byte memx159 to register64
clc;
adcx r14, r15; loading flag
adcx rdi, r8
movzx r14, r13b; x140, copying x116 here, cause x116 is needed in a reg for other than x140, namely all: , x140, size: 1
mov r8, 0x0 ; moving imm to reg
adox r14, r8
adcx r11, rax
adcx r12, r14
inc r15; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r8; loading flag
adox rsi, [ rsp + 0x78 ]
setc r9b; spill CF x165 to reg (r9)
movzx r13, byte [ rsp + 0x68 ]; load byte memx182 to register64
clc;
adcx r13, r8; loading flag
adcx rdi, [ rsp + 0x88 ]
adox rdx, r15
adcx rsi, r11
adcx rdx, r12
movzx r13, r9b; x189, copying x165 here, cause x165 is needed in a reg for other than x189, namely all: , x189, size: 1
adc r13, 0x0
movzx rax, byte [ rsp + 0x80 ]; x191, copying x191 here, cause x191 is needed in a reg for other than x191, namely all: , x192--x193, size: 1
add rax, -0x1
mov rax, rdi; x192, copying x183 here, cause x183 is needed in a reg for other than x192, namely all: , x192--x193, x201, size: 2
mov r14, 0xffffffff00000000 ; moving imm to reg
sbb rax, r14
mov r11, rsi; x194, copying x185 here, cause x185 is needed in a reg for other than x194, namely all: , x194--x195, x202, size: 2
mov r9, 0xffffffffffffffff ; moving imm to reg
sbb r11, r9
mov r12, rdx; x196, copying x187 here, cause x187 is needed in a reg for other than x196, namely all: , x203, x196--x197, size: 2
sbb r12, rbp
sbb r13, 0x00000000
cmovc rax, rdi; if CF, x201<- x183 (nzVar)
mov r13, [ rsp + 0x60 ]; x200, copying x190 here, cause x190 is needed in a reg for other than x200, namely all: , x200, size: 1
cmovc r13, rcx; if CF, x200<- x181 (nzVar)
cmovc r11, rsi; if CF, x202<- x185 (nzVar)
mov rcx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rcx + 0x10 ], r11; out1[2] = x202
mov [ rcx + 0x0 ], r13; out1[0] = x200
cmovc r12, rdx; if CF, x203<- x187 (nzVar)
mov [ rcx + 0x8 ], rax; out1[1] = x201
mov [ rcx + 0x18 ], r12; out1[3] = x203
mov rbx, [ rsp + 0x90 ]; restoring from stack
mov rbp, [ rsp + 0x98 ]; restoring from stack
mov r12, [ rsp + 0xa0 ]; restoring from stack
mov r13, [ rsp + 0xa8 ]; restoring from stack
mov r14, [ rsp + 0xb0 ]; restoring from stack
mov r15, [ rsp + 0xb8 ]; restoring from stack
add rsp, 0xc0 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 79.025, best 56.330935251798564, lastGood 56.43478260869565
; seed 2553258791112417 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 685016 ms / 60000 runs=> 11.416933333333333ms/run
; Time spent for assembling and measureing (initial batch_size=139, initial num_batches=101): 148837 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2172752169292396
; number reverted permutation/ tried permutation: 23884 / 30001 =79.611%
; number reverted decision/ tried decision: 22477 / 30000 =74.923%