SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0xd0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xa0 ], rbx; saving to stack
mov [ rsp + 0xa8 ], rbp; saving to stack
mov [ rsp + 0xb0 ], r12; saving to stack
mov [ rsp + 0xb8 ], r13; saving to stack
mov [ rsp + 0xc0 ], r14; saving to stack
mov [ rsp + 0xc8 ], r15; saving to stack
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov rdx, rax; x3 to rdx
mulx rax, r10, [ rsi + 0x18 ]; x154, x153<- x3 * arg1[3]
mulx r11, rbx, [ rsi + 0x8 ]; x158, x157<- x3 * arg1[1]
mulx rbp, r12, [ rsi + 0x10 ]; x156, x155<- x3 * arg1[2]
mulx rdx, r13, [ rsi + 0x0 ]; x160, x159<- x3 * arg1[0]
xor r14, r14
adox rbx, rdx
mov r15, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, r15; x2 to rdx
mulx r15, rcx, [ rsi + 0x8 ]; x105, x104<- x2 * arg1[1]
mulx r8, r9, [ rsi + 0x18 ]; x101, x100<- x2 * arg1[3]
adox r12, r11
adox r10, rbp
mulx r11, rbp, [ rsi + 0x10 ]; x103, x102<- x2 * arg1[2]
mov r14, [ rsi + 0x0 ]; load m64 x4 to register64
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rdx, rdi, [ rsi + 0x0 ]; x107, x106<- x2 * arg1[0]
mov [ rsp + 0x8 ], r10; spilling x165 to mem
mov r10, 0x0 ; moving imm to reg
adox rax, r10
adcx rcx, rdx
mov rdx, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rbp, r15
mulx r15, r10, [ rsi + 0x0 ]; x54, x53<- x1 * arg1[0]
adcx r9, r11
mov [ rsp + 0x10 ], rax; spilling x167 to mem
mulx r11, rax, [ rsi + 0x10 ]; x50, x49<- x1 * arg1[2]
mov [ rsp + 0x18 ], r12; spilling x163 to mem
mov [ rsp + 0x20 ], rbx; spilling x161 to mem
mulx r12, rbx, [ rsi + 0x18 ]; x48, x47<- x1 * arg1[3]
adc r8, 0x0
mov [ rsp + 0x28 ], r13; spilling x159 to mem
mulx rdx, r13, [ rsi + 0x8 ]; x52, x51<- x1 * arg1[1]
add r13, r15; could be done better, if r0 has been u8 as well
adcx rax, rdx
mov rdx, r14; x4 to rdx
mulx r14, r15, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mov [ rsp + 0x30 ], r8; spilling x114 to mem
mov r8, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r8; 0xd838091dd2253531, swapping with x4, which is currently in rdx
mov [ rsp + 0x38 ], r9; spilling x112 to mem
mov [ rsp + 0x40 ], rbp; spilling x110 to mem
mulx r9, rbp, r15; _, x20<- x11 * 0xd838091dd2253531
mov r9, rdx; preserving value of 0xd838091dd2253531 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x48 ], rcx; spilling x108 to mem
mov [ rsp + 0x50 ], rax; spilling x57 to mem
mulx rcx, rax, r8; x10, x9<- x4 * arg1[1]
adcx rbx, r11
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mulx r11, r9, rbp; x29, x28<- x20 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x58 ], rbx; spilling x59 to mem
mov [ rsp + 0x60 ], rdi; spilling x106 to mem
mulx rbx, rdi, rbp; x27, x26<- x20 * 0xffffffffffffffff
adc r12, 0x0
test al, al
adox rax, r14
adcx rdi, r11
setc r14b; spill CF x31 to reg (r14)
clc;
adcx r9, r15
adcx rdi, rax
setc r9b; spill CF x40 to reg (r9)
clc;
adcx r10, rdi
mov r15, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r15; 0xd838091dd2253531, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r11, rax, r10; _, x72<- x62 * 0xd838091dd2253531
xchg rdx, rax; x72, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r11, rdi, r15; x79, x78<- x72 * 0xffffffffffffffff
mov r15, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x68 ], r12; spilling x61 to mem
mulx rax, r12, r15; x81, x80<- x72 * 0xfffffffefffffc2f
setc r15b; spill CF x63 to reg (r15)
clc;
adcx r12, r10
mov r12, rdx; preserving value of x72 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x70 ], r11; spilling x79 to mem
mulx r10, r11, r8; x8, x7<- x4 * arg1[2]
adox r11, rcx
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x78 ], r10; spilling x8 to mem
mulx rcx, r10, rbp; x25, x24<- x20 * 0xffffffffffffffff
setc dl; spill CF x90 to reg (rdx)
clc;
adcx rdi, rax
setc al; spill CF x83 to reg (rax)
clc;
mov [ rsp + 0x80 ], rcx; spilling x25 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rcx; loading flag
adcx rbx, r10
seto r14b; spill OF x16 to reg (r14)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, r10; loading flag
adox r11, rbx
seto r9b; spill OF x42 to reg (r9)
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r15, r15b
adox r15, rcx; loading flag
adox r11, r13
seto r10b; spill OF x65 to reg (r10)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r13; loading flag
adox r11, rdi
seto r15b; spill OF x92 to reg (r15)
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, [ rsp + 0x60 ]
mov rdi, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r11; x115 to rdx
mulx r11, rbx, rdi; _, x125<- x115 * 0xd838091dd2253531
mov r11, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rbx; x125, swapping with x115, which is currently in rdx
mulx rcx, r13, r11; x134, x133<- x125 * 0xfffffffefffffc2f
seto r11b; spill OF x116 to reg (r11)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbx
mov r13, rdx; preserving value of x125 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r8, rbx, r8; x6, x5<- x4 * arg1[3]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x88 ], r11b; spilling byte x116 to mem
mulx rdi, r11, r12; x77, x76<- x72 * 0xffffffffffffffff
mov byte [ rsp + 0x90 ], r15b; spilling byte x92 to mem
mulx rbp, r15, rbp; x23, x22<- x20 * 0xffffffffffffffff
mov rdx, [ rsp + 0x80 ]; x34, copying x25 here, cause x25 is needed in a reg for other than x34, namely all: , x34--x35, size: 1
adcx rdx, r15
seto r15b; spill OF x143 to reg (r15)
mov byte [ rsp + 0x98 ], r10b; spilling byte x65 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r10; loading flag
adox rbx, [ rsp + 0x78 ]
mov r14, 0x0 ; moving imm to reg
adcx rbp, r14
adox r8, r14
add al, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc al; since that has deps, resore it whereever it was
adcx r11, [ rsp + 0x70 ]
movzx r9, r9b
adox r9, r10; loading flag
adox rbx, rdx
mov rax, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; 0xffffffffffffffff to rdx
mulx r12, rax, r12; x75, x74<- x72 * 0xffffffffffffffff
adcx rax, rdi
adcx r12, r14
adox rbp, r8
mulx r9, rdi, r13; x132, x131<- x125 * 0xffffffffffffffff
clc;
adcx rdi, rcx
setc cl; spill CF x136 to reg (rcx)
movzx r8, byte [ rsp + 0x98 ]; load byte memx65 to register64
clc;
adcx r8, r10; loading flag
adcx rbx, [ rsp + 0x50 ]
mov r8, [ rsp + 0x58 ]; x68, copying x59 here, cause x59 is needed in a reg for other than x68, namely all: , x68--x69, size: 1
adcx r8, rbp
setc bpl; spill CF x70 to reg (rbp)
movzx rbp, bpl; spilling a flag to reg cause it has deps 
adox rbp, [ rsp + 0x68 ]; OF should have been spilled if it had deps, CF should have been spilled into rbp and into another reg, if it has had other deps than this one.
movzx r14, byte [ rsp + 0x90 ]; load byte memx92 to register64
clc;
adcx r14, r10; loading flag
adcx rbx, r11
adcx rax, r8
seto r14b; spill OF x71 to reg (r14)
movzx r11, byte [ rsp + 0x88 ]; load byte memx116 to register64
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
adox r11, r8; loading flag
adox rbx, [ rsp + 0x48 ]
mulx r11, r10, r13; x130, x129<- x125 * 0xffffffffffffffff
adcx r12, rbp
mov rbp, [ rsp + 0x40 ]; x119, copying x110 here, cause x110 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adox rbp, rax
setc al; spill CF x98 to reg (rax)
clc;
movzx rcx, cl
adcx rcx, r8; loading flag
adcx r9, r10
mulx r13, rcx, r13; x128, x127<- x125 * 0xffffffffffffffff
movzx r10, al; x99, copying x98 here, cause x98 is needed in a reg for other than x99, namely all: , x99, size: 1
movzx r14, r14b
lea r10, [ r10 + r14 ]
mov r14, [ rsp + 0x38 ]; x121, copying x112 here, cause x112 is needed in a reg for other than x121, namely all: , x121--x122, size: 1
adox r14, r12
mov rax, [ rsp + 0x30 ]; x123, copying x114 here, cause x114 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adox rax, r10
adcx rcx, r11
mov r11, 0x0 ; moving imm to reg
adcx r13, r11
clc;
movzx r15, r15b
adcx r15, r8; loading flag
adcx rbx, rdi
seto r15b; spill OF x124 to reg (r15)
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, [ rsp + 0x28 ]
adcx r9, rbp
mov r12, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r12; 0xd838091dd2253531, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbp, r10, rbx; _, x178<- x168 * 0xd838091dd2253531
adcx rcx, r14
mov rbp, [ rsp + 0x20 ]; x170, copying x161 here, cause x161 is needed in a reg for other than x170, namely all: , x170--x171, size: 1
adox rbp, r9
mov r14, [ rsp + 0x18 ]; x172, copying x163 here, cause x163 is needed in a reg for other than x172, namely all: , x172--x173, size: 1
adox r14, rcx
adcx r13, rax
mov rax, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r10; x178, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r9, rcx, rax; x187, x186<- x178 * 0xfffffffefffffc2f
movzx r11, r15b; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
mov rdi, 0x0 ; moving imm to reg
adcx r11, rdi
mulx r15, rdi, r12; x185, x184<- x178 * 0xffffffffffffffff
clc;
adcx rdi, r9
seto r9b; spill OF x173 to reg (r9)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, rbx
adox rdi, rbp
mulx rcx, rbx, r12; x183, x182<- x178 * 0xffffffffffffffff
adcx rbx, r15
adox rbx, r14
setc bpl; spill CF x191 to reg (rbp)
seto r14b; spill OF x200 to reg (r14)
mov r15, rdi; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
sub r15, rax
dec r8; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r9, r9b
adox r9, r8; loading flag
adox r13, [ rsp + 0x8 ]
mulx rdx, r9, r12; x181, x180<- x178 * 0xffffffffffffffff
mov r8, [ rsp + 0x10 ]; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adox r8, r11
seto r11b; spill OF x177 to reg (r11)
mov r10, rbx; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x217, x208--x209, size: 2
sbb r10, r12
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rax; loading flag
adox rcx, r9
mov rbp, 0x0 ; moving imm to reg
adox rdx, rbp
inc rax; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbp; loading flag
adox r13, rcx
adox rdx, r8
movzx r14, r11b; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
adox r14, rax
mov r9, r13; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x210--x211, x218, size: 2
sbb r9, r12
mov r11, rdx; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x212--x213, x219, size: 2
sbb r11, r12
sbb r14, 0x00000000
cmovc r9, r13; if CF, x218<- x201 (nzVar)
cmovc r10, rbx; if CF, x217<- x199 (nzVar)
cmovc r15, rdi; if CF, x216<- x197 (nzVar)
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x10 ], r9; out1[2] = x218
cmovc r11, rdx; if CF, x219<- x203 (nzVar)
mov [ r14 + 0x18 ], r11; out1[3] = x219
mov [ r14 + 0x0 ], r15; out1[0] = x216
mov [ r14 + 0x8 ], r10; out1[1] = x217
mov rbx, [ rsp + 0xa0 ]; restoring from stack
mov rbp, [ rsp + 0xa8 ]; restoring from stack
mov r12, [ rsp + 0xb0 ]; restoring from stack
mov r13, [ rsp + 0xb8 ]; restoring from stack
mov r14, [ rsp + 0xc0 ]; restoring from stack
mov r15, [ rsp + 0xc8 ]; restoring from stack
add rsp, 0xd0 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4801 MHz
; first cyclecount 101.27, best 79.29896907216495, lastGood 79.90721649484536
; seed 1129172745277633 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 868962 ms / 60000 runs=> 14.4827ms/run
; Time spent for assembling and measureing (initial batch_size=97, initial num_batches=101): 101892 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.11725714127890517
; number reverted permutation/ tried permutation: 23481 / 29962 =78.369%
; number reverted decision/ tried decision: 21452 / 30039 =71.414%