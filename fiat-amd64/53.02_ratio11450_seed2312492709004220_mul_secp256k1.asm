SECTION .text
	GLOBAL mul_secp256k1
mul_secp256k1:
sub rsp, 0x110 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xe0 ], rbx; saving to stack
mov [ rsp + 0xe8 ], rbp; saving to stack
mov [ rsp + 0xf0 ], r12; saving to stack
mov [ rsp + 0xf8 ], r13; saving to stack
mov [ rsp + 0x100 ], r14; saving to stack
mov [ rsp + 0x108 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rbp, rax; x12, x11<- x4 * arg2[0]
mov r12, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r12; 0xd838091dd2253531 to rdx
mulx r12, r13, rbp; _, x20<- x11 * 0xd838091dd2253531
mov r12, rdx; preserving value of 0xd838091dd2253531 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx r14, r15, rax; x10, x9<- x4 * arg2[1]
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; x20 to rdx
mulx r13, r8, rcx; x27, x26<- x20 * 0xffffffffffffffff
xor r9, r9
adox r15, rbx
mov rbx, 0xfffffffefffffc2f ; moving imm to reg
mulx r9, rcx, rbx; x29, x28<- x20 * 0xfffffffefffffc2f
adcx r8, r9
seto r9b; spill OF x14 to reg (r9)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, rbp
mov rcx, rdx; preserving value of x20 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r12, r10; x54, x53<- x1 * arg2[0]
adox r8, r15
setc r15b; spill CF x31 to reg (r15)
clc;
adcx r12, r8
mov r8, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r8; 0xd838091dd2253531 to rdx
mulx r8, rbx, r12; _, x72<- x62 * 0xd838091dd2253531
mov r8, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r8; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r8, rdi, rbx; x81, x80<- x72 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x8 ], r14; spilling x10 to mem
mov byte [ rsp + 0x10 ], r9b; spilling byte x14 to mem
mulx r14, r9, rbx; x77, x76<- x72 * 0xffffffffffffffff
mov [ rsp + 0x18 ], rax; spilling x4 to mem
mov [ rsp + 0x20 ], rdi; spilling x80 to mem
mulx rax, rdi, rbx; x79, x78<- x72 * 0xffffffffffffffff
mov [ rsp + 0x28 ], r13; spilling x27 to mem
mulx rbx, r13, rbx; x75, x74<- x72 * 0xffffffffffffffff
setc dl; spill CF x63 to reg (rdx)
clc;
adcx rdi, r8
adcx r9, rax
adcx r13, r14
mov r8, 0x0 ; moving imm to reg
adcx rbx, r8
xchg rdx, r10; x1, swapping with x63, which is currently in rdx
mulx r14, rax, [ r11 + 0x8 ]; x52, x51<- x1 * arg2[1]
mov r8, [ rsi + 0x10 ]; load m64 x2 to register64
clc;
adcx rax, rbp
mov [ rsp + 0x30 ], rbx; spilling x88 to mem
mulx rbp, rbx, [ r11 + 0x10 ]; x50, x49<- x1 * arg2[2]
adcx rbx, r14
mulx rdx, r14, [ r11 + 0x18 ]; x48, x47<- x1 * arg2[3]
adcx r14, rbp
mov rbp, rdx; preserving value of x48 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x38 ], r13; spilling x86 to mem
mov [ rsp + 0x40 ], r9; spilling x84 to mem
mulx r13, r9, r8; x105, x104<- x2 * arg2[1]
mov rdx, r8; x2 to rdx
mov [ rsp + 0x48 ], r14; spilling x59 to mem
mulx r8, r14, [ r11 + 0x18 ]; x101, x100<- x2 * arg2[3]
mov [ rsp + 0x50 ], rbx; spilling x57 to mem
mov rbx, 0x0 ; moving imm to reg
adcx rbp, rbx
mov [ rsp + 0x58 ], rbp; spilling x61 to mem
mulx rbx, rbp, [ r11 + 0x0 ]; x107, x106<- x2 * arg2[0]
clc;
adcx r9, rbx
mulx rdx, rbx, [ r11 + 0x10 ]; x103, x102<- x2 * arg2[2]
adcx rbx, r13
adcx r14, rdx
mov r13, 0x0 ; moving imm to reg
adcx r8, r13
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x60 ], r8; spilling x114 to mem
mulx r13, r8, rcx; x25, x24<- x20 * 0xffffffffffffffff
mov [ rsp + 0x68 ], r14; spilling x112 to mem
mulx rcx, r14, rcx; x23, x22<- x20 * 0xffffffffffffffff
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rdx; loading flag
adcx r8, [ rsp + 0x28 ]
adcx r14, r13
setc r15b; spill CF x35 to reg (r15)
clc;
adcx r12, [ rsp + 0x20 ]
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mulx r12, r13, [ rsp + 0x18 ]; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x70 ], rbx; spilling x110 to mem
setc bl; spill CF x90 to reg (rbx)
mov [ rsp + 0x78 ], r9; spilling x108 to mem
movzx r9, byte [ rsp + 0x10 ]; load byte memx14 to register64
clc;
mov [ rsp + 0x80 ], r14; spilling x34 to mem
mov r14, -0x1 ; moving imm to reg
adcx r9, r14; loading flag
adcx r13, [ rsp + 0x8 ]
adox r8, r13
seto r9b; spill OF x42 to reg (r9)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r13; loading flag
adox r8, rax
seto r10b; spill OF x65 to reg (r10)
dec r14; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rbx, bl
adox rbx, r14; loading flag
adox r8, rdi
seto r13b; spill OF x92 to reg (r13)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r8
mov rdi, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rbp; x115 to rdx
mulx rbp, rax, rdi; _, x125<- x115 * 0xd838091dd2253531
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rax; x125, swapping with x115, which is currently in rdx
mulx rbx, r8, rbp; x132, x131<- x125 * 0xffffffffffffffff
movzx r14, r15b; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
lea r14, [ r14 + rcx ]
mov rcx, 0xfffffffefffffc2f ; moving imm to reg
mulx r15, rdi, rcx; x134, x133<- x125 * 0xfffffffefffffc2f
mov [ rsp + 0x88 ], rdi; spilling x133 to mem
mulx rcx, rdi, rbp; x128, x127<- x125 * 0xffffffffffffffff
seto bpl; spill OF x116 to reg (rbp)
mov byte [ rsp + 0x90 ], r13b; spilling byte x92 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r13, r15; x130, x129<- x125 * 0xffffffffffffffff
adox r13, rbx
adox rdi, rdx
mov rdx, [ rsp + 0x18 ]; x4 to rdx
mulx rdx, rbx, [ r11 + 0x18 ]; x6, x5<- x4 * arg2[3]
adcx rbx, r12
mov r12, 0x0 ; moving imm to reg
adcx rdx, r12
adox rcx, r12
add r9b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r9b; since that has deps, resore it whereever it was
adcx rbx, [ rsp + 0x80 ]
mov r9, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r9; loading flag
adox rbx, [ rsp + 0x50 ]
adcx r14, rdx
mov r10, [ rsi + 0x18 ]; load m64 x3 to register64
mov rdx, [ rsp + 0x48 ]; x68, copying x59 here, cause x59 is needed in a reg for other than x68, namely all: , x68--x69, size: 1
adox rdx, r14
setc r14b; spill CF x70 to reg (r14)
movzx r14, r14b; spilling a flag to reg cause it has deps 
adox r14, [ rsp + 0x58 ]; OF should have been spilled if it had deps, CF should have been spilled into r14 and into another reg, if it has had other deps than this one.
movzx r12, byte [ rsp + 0x90 ]; load byte memx92 to register64
clc;
adcx r12, r9; loading flag
adcx rbx, [ rsp + 0x40 ]
mov r12, [ rsp + 0x38 ]; x95, copying x86 here, cause x86 is needed in a reg for other than x95, namely all: , x95--x96, size: 1
adcx r12, rdx
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx r9, r15, r10; x160, x159<- x3 * arg2[0]
mov [ rsp + 0x98 ], rcx; spilling x141 to mem
mov rcx, [ rsp + 0x30 ]; x97, copying x88 here, cause x88 is needed in a reg for other than x97, namely all: , x97--x98, size: 1
adcx rcx, r14
seto r14b; spill OF x99 to reg (r14)
adc r14b, 0x0
movzx r14, r14b
add bpl, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto bpl; since that has deps, resore it whereever it was
adox rbx, [ rsp + 0x78 ]
mov rbp, [ rsp + 0x70 ]; x119, copying x110 here, cause x110 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adox rbp, r12
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mov byte [ rsp + 0xa0 ], r14b; spilling byte x99 to mem
mulx r12, r14, r10; x158, x157<- x3 * arg2[1]
adcx rax, [ rsp + 0x88 ]
adcx r8, rbx
adcx r13, rbp
setc al; spill CF x147 to reg (rax)
clc;
adcx r14, r9
setc r9b; spill CF x162 to reg (r9)
clc;
adcx r15, r8
adcx r14, r13
mov rbx, 0xd838091dd2253531 ; moving imm to reg
mov rdx, rbx; 0xd838091dd2253531 to rdx
mulx rbx, rbp, r15; _, x178<- x168 * 0xd838091dd2253531
mov rbx, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rbp; x178, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r8, r13, rbx; x187, x186<- x178 * 0xfffffffefffffc2f
setc bl; spill CF x171 to reg (rbx)
clc;
adcx r13, r15
mov r13, 0xffffffffffffffff ; moving imm to reg
mulx r15, rbp, r13; x185, x184<- x178 * 0xffffffffffffffff
mov r13, [ rsp + 0x68 ]; x121, copying x112 here, cause x112 is needed in a reg for other than x121, namely all: , x121--x122, size: 1
adox r13, rcx
seto cl; spill OF x122 to reg (rcx)
mov [ rsp + 0xa8 ], r15; spilling x185 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r15; loading flag
adox r13, rdi
seto dil; spill OF x149 to reg (rdi)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r8
adcx rbp, r14
setc al; spill CF x198 to reg (rax)
seto r14b; spill OF x189 to reg (r14)
mov r8, rbp; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov byte [ rsp + 0xb0 ], dil; spilling byte x149 to mem
mov rdi, 0xfffffffefffffc2f ; moving imm to reg
sub r8, rdi
mov r15, rdx; preserving value of x178 into a new reg
mov rdx, [ r11 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0xb8 ], r8; spilling x206 to mem
mulx rdi, r8, r10; x156, x155<- x3 * arg2[2]
mov [ rsp + 0xc0 ], rdi; spilling x156 to mem
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rdi; loading flag
adox r12, r8
setc r9b; spill CF x207 to reg (r9)
clc;
movzx rbx, bl
adcx rbx, rdi; loading flag
adcx r13, r12
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbx; 0xffffffffffffffff to rdx
mulx rbx, r8, r15; x183, x182<- x178 * 0xffffffffffffffff
setc r12b; spill CF x173 to reg (r12)
clc;
movzx r14, r14b
adcx r14, rdi; loading flag
adcx r8, [ rsp + 0xa8 ]
setc r14b; spill CF x191 to reg (r14)
clc;
movzx rax, al
adcx rax, rdi; loading flag
adcx r13, r8
movzx rax, byte [ rsp + 0xa0 ]; load byte memx99 to register64
setc r8b; spill CF x200 to reg (r8)
clc;
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx rax, [ rsp + 0x60 ]
mov rcx, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ r11 + 0x18 ]; saving arg2[3] in rdx.
mulx r10, rdi, r10; x154, x153<- x3 * arg2[3]
mov byte [ rsp + 0xc8 ], r8b; spilling byte x200 to mem
setc r8b; spill CF x124 to reg (r8)
mov [ rsp + 0xd0 ], rbx; spilling x183 to mem
seto bl; spill OF x164 to reg (rbx)
mov byte [ rsp + 0xd8 ], r14b; spilling byte x191 to mem
movzx r14, r9b; x207, copying x207 here, cause x207 is needed in a reg for other than x207, namely all: , x208--x209, size: 1
add r14, -0x1
mov r14, r13; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
sbb r14, rcx
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r9; loading flag
adox rdi, [ rsp + 0xc0 ]
setc bl; spill CF x209 to reg (rbx)
movzx r9, byte [ rsp + 0xb0 ]; load byte memx149 to register64
clc;
mov rcx, -0x1 ; moving imm to reg
adcx r9, rcx; loading flag
adcx rax, [ rsp + 0x98 ]
movzx r9, r8b; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
mov rcx, 0x0 ; moving imm to reg
adcx r9, rcx
mov r8, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r15, r8, r15; x181, x180<- x178 * 0xffffffffffffffff
adox r10, rcx
add r12b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r12b; since that has deps, resore it whereever it was
adcx rax, rdi
movzx r12, byte [ rsp + 0xd8 ]; load byte memx191 to register64
mov rdi, -0x1 ; moving imm to reg
adox r12, rdi; loading flag
adox r8, [ rsp + 0xd0 ]
adcx r10, r9
setc r12b; spill CF x177 to reg (r12)
movzx r9, byte [ rsp + 0xc8 ]; load byte memx200 to register64
clc;
adcx r9, rdi; loading flag
adcx rax, r8
adox r15, rcx
adcx r15, r10
movzx r9, r12b; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
adc r9, 0x0
movzx r8, bl; x209, copying x209 here, cause x209 is needed in a reg for other than x209, namely all: , x210--x211, size: 1
add r8, -0x1
mov rbx, rax; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb rbx, rdx
mov r8, r15; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb r8, rdx
sbb r9, 0x00000000
cmovc r14, r13; if CF, x217<- x199 (nzVar)
mov r9, [ rsp + 0xb8 ]; x216, copying x206 here, cause x206 is needed in a reg for other than x216, namely all: , x216, size: 1
cmovc r9, rbp; if CF, x216<- x197 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x8 ], r14; out1[1] = x217
cmovc r8, r15; if CF, x219<- x203 (nzVar)
cmovc rbx, rax; if CF, x218<- x201 (nzVar)
mov [ rbp + 0x18 ], r8; out1[3] = x219
mov [ rbp + 0x0 ], r9; out1[0] = x216
mov [ rbp + 0x10 ], rbx; out1[2] = x218
mov rbx, [ rsp + 0xe0 ]; restoring from stack
mov rbp, [ rsp + 0xe8 ]; restoring from stack
mov r12, [ rsp + 0xf0 ]; restoring from stack
mov r13, [ rsp + 0xf8 ]; restoring from stack
mov r14, [ rsp + 0x100 ]; restoring from stack
mov r15, [ rsp + 0x108 ]; restoring from stack
add rsp, 0x110 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 56.935, best 51.163636363636364, lastGood 53.015625
; seed 2312492709004220 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1388511 ms / 60000 runs=> 23.14185ms/run
; Time spent for assembling and measureing (initial batch_size=160, initial num_batches=101): 316103 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2276561006718708
; number reverted permutation/ tried permutation: 26814 / 30149 =88.938%
; number reverted decision/ tried decision: 22824 / 29852 =76.457%