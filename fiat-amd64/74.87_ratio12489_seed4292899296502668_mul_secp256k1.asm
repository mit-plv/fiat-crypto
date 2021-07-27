SECTION .text
	GLOBAL mul_secp256k1
mul_secp256k1:
sub rsp, 0xd0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0xa0 ], rbx; saving to stack
mov [ rsp + 0xa8 ], rbp; saving to stack
mov [ rsp + 0xb0 ], r12; saving to stack
mov [ rsp + 0xb8 ], r13; saving to stack
mov [ rsp + 0xc0 ], r14; saving to stack
mov [ rsp + 0xc8 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov r10, [ rsi + 0x0 ]; load m64 x4 to register64
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx rbx, rbp, r10; x10, x9<- x4 * arg2[1]
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx r12, r13, r10; x12, x11<- x4 * arg2[0]
mov r14, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r13; x11 to rdx
mulx r13, r15, r14; _, x20<- x11 * 0xd838091dd2253531
xchg rdx, rax; x1, swapping with x11, which is currently in rdx
mulx r13, rcx, [ r11 + 0x0 ]; x54, x53<- x1 * arg2[0]
mov r8, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r15; x20, swapping with x1, which is currently in rdx
mulx r9, r14, r8; x29, x28<- x20 * 0xfffffffefffffc2f
test al, al
adox r14, rax
adcx rbp, r12
mov r14, 0xffffffffffffffff ; moving imm to reg
mulx r12, rax, r14; x27, x26<- x20 * 0xffffffffffffffff
setc r14b; spill CF x14 to reg (r14)
clc;
adcx rax, r9
adox rax, rbp
setc r9b; spill CF x31 to reg (r9)
clc;
adcx rcx, rax
mov rbp, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rbp; 0xd838091dd2253531, swapping with x20, which is currently in rdx
mulx rax, r8, rcx; _, x72<- x62 * 0xd838091dd2253531
mov rax, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; x20, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbp, rdi, rax; x25, x24<- x20 * 0xffffffffffffffff
mov rax, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r8; x72, swapping with x20, which is currently in rdx
mov [ rsp + 0x8 ], rsi; spilling arg1 to mem
mov [ rsp + 0x10 ], rbp; spilling x25 to mem
mulx rsi, rbp, rax; x81, x80<- x72 * 0xfffffffefffffc2f
setc al; spill CF x63 to reg (rax)
clc;
adcx rbp, rcx
setc bpl; spill CF x90 to reg (rbp)
clc;
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rcx; loading flag
adcx r12, rdi
mov r9, rdx; preserving value of x72 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx rdi, rcx, r15; x52, x51<- x1 * arg2[1]
mov rdx, r10; x4 to rdx
mov [ rsp + 0x18 ], rdi; spilling x52 to mem
mulx r10, rdi, [ r11 + 0x10 ]; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x20 ], r10; spilling x8 to mem
setc r10b; spill CF x33 to reg (r10)
clc;
mov byte [ rsp + 0x28 ], bpl; spilling byte x90 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, rbp; loading flag
adcx rbx, rdi
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mulx rdi, rbp, r9; x79, x78<- x72 * 0xffffffffffffffff
adox r12, rbx
setc bl; spill CF x16 to reg (rbx)
clc;
adcx rcx, r13
setc r13b; spill CF x56 to reg (r13)
clc;
adcx rbp, rsi
setc sil; spill CF x83 to reg (rsi)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx r12, rcx
setc al; spill CF x65 to reg (rax)
movzx rcx, byte [ rsp + 0x28 ]; load byte memx90 to register64
clc;
adcx rcx, rdx; loading flag
adcx r12, rbp
mov rdx, r14; x4 to rdx
mulx rdx, r14, [ r11 + 0x18 ]; x6, x5<- x4 * arg2[3]
mov rcx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; 0xffffffffffffffff, swapping with x6, which is currently in rdx
mov [ rsp + 0x30 ], r12; spilling x91 to mem
mulx rbp, r12, r9; x75, x74<- x72 * 0xffffffffffffffff
mov [ rsp + 0x38 ], rbp; spilling x75 to mem
mulx r8, rbp, r8; x23, x22<- x20 * 0xffffffffffffffff
xchg rdx, r15; x1, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x40 ], r12; spilling x74 to mem
mulx r15, r12, [ r11 + 0x10 ]; x50, x49<- x1 * arg2[2]
mov [ rsp + 0x48 ], r15; spilling x50 to mem
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mov byte [ rsp + 0x50 ], al; spilling byte x65 to mem
mulx r9, rax, r9; x77, x76<- x72 * 0xffffffffffffffff
setc dl; spill CF x92 to reg (rdx)
clc;
mov [ rsp + 0x58 ], r9; spilling x77 to mem
mov r9, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, r9; loading flag
adcx rbp, [ rsp + 0x10 ]
setc r10b; spill CF x35 to reg (r10)
clc;
movzx rbx, bl
adcx rbx, r9; loading flag
adcx r14, [ rsp + 0x20 ]
adox rbp, r14
seto bl; spill OF x44 to reg (rbx)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox r12, [ rsp + 0x18 ]
adcx rcx, r9
mov r13, [ rsp + 0x8 ]; load m64 arg1 to register64
mov r9, [ r13 + 0x10 ]; load m64 x2 to register64
clc;
movzx rsi, sil
adcx rsi, r14; loading flag
adcx rdi, rax
movzx rsi, r10b; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
lea rsi, [ rsi + r8 ]
setc r8b; spill CF x85 to reg (r8)
movzx rax, byte [ rsp + 0x50 ]; load byte memx65 to register64
clc;
adcx rax, r14; loading flag
adcx rbp, r12
setc al; spill CF x67 to reg (rax)
clc;
movzx rbx, bl
adcx rbx, r14; loading flag
adcx rcx, rsi
mov r10, [ rsp + 0x40 ]; load m64 x74 to register64
setc bl; spill CF x46 to reg (rbx)
clc;
movzx r8, r8b
adcx r8, r14; loading flag
adcx r10, [ rsp + 0x58 ]
xchg rdx, r15; x1, swapping with x92, which is currently in rdx
mulx rdx, r12, [ r11 + 0x18 ]; x48, x47<- x1 * arg2[3]
mov r8, [ rsp + 0x48 ]; x59, copying x50 here, cause x50 is needed in a reg for other than x59, namely all: , x59--x60, size: 1
adox r8, r12
mov rsi, 0x0 ; moving imm to reg
adox rdx, rsi
mov r12, [ rsp + 0x38 ]; x88, copying x75 here, cause x75 is needed in a reg for other than x88, namely all: , x88, size: 1
adc r12, 0x0
add r15b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r15b; since that has deps, resore it whereever it was
adox rbp, rdi
movzx rax, al
adcx rax, r14; loading flag
adcx rcx, r8
adox r10, rcx
mov r15, rdx; preserving value of x61 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx rdi, rax, r9; x107, x106<- x2 * arg2[0]
movzx r8, bl; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adcx r8, r15
mov rdx, r9; x2 to rdx
mulx r9, rbx, [ r11 + 0x10 ]; x103, x102<- x2 * arg2[2]
adox r12, r8
mulx r15, rcx, [ r11 + 0x8 ]; x105, x104<- x2 * arg2[1]
setc r8b; spill CF x71 to reg (r8)
clc;
adcx rcx, rdi
mulx rdx, rdi, [ r11 + 0x18 ]; x101, x100<- x2 * arg2[3]
adcx rbx, r15
adcx rdi, r9
adcx rdx, rsi
clc;
adcx rax, [ rsp + 0x30 ]
mov r9, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r9; 0xd838091dd2253531, swapping with x114, which is currently in rdx
mulx r15, rsi, rax; _, x125<- x115 * 0xd838091dd2253531
mov r15, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r15; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r14, r15, rsi; x134, x133<- x125 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x60 ], r9; spilling x114 to mem
mov [ rsp + 0x68 ], rdi; spilling x112 to mem
mulx r9, rdi, rsi; x132, x131<- x125 * 0xffffffffffffffff
mov [ rsp + 0x70 ], r9; spilling x132 to mem
mov [ rsp + 0x78 ], r12; spilling x97 to mem
mulx r9, r12, rsi; x130, x129<- x125 * 0xffffffffffffffff
adcx rcx, rbp
setc bpl; spill CF x118 to reg (rbp)
clc;
adcx r15, rax
mulx rsi, r15, rsi; x128, x127<- x125 * 0xffffffffffffffff
setc al; spill CF x143 to reg (rax)
clc;
adcx rdi, r14
movzx r14, r8b; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
mov rdx, 0x0 ; moving imm to reg
adox r14, rdx
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbp, bpl
adox rbp, rdx; loading flag
adox r10, rbx
mov r8, [ rsp + 0x68 ]; load m64 x112 to register64
mov rbx, [ rsp + 0x78 ]; x121, copying x97 here, cause x97 is needed in a reg for other than x121, namely all: , x121--x122, size: 1
adox rbx, r8
mov r8, [ rsp + 0x70 ]; x137, copying x132 here, cause x132 is needed in a reg for other than x137, namely all: , x137--x138, size: 1
adcx r8, r12
mov r12, [ r13 + 0x18 ]; load m64 x3 to register64
mov rdx, r12; x3 to rdx
mulx r12, rbp, [ r11 + 0x0 ]; x160, x159<- x3 * arg2[0]
adcx r15, r9
mov r9, [ rsp + 0x60 ]; x123, copying x114 here, cause x114 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adox r9, r14
seto r14b; spill OF x124 to reg (r14)
mov [ rsp + 0x80 ], rbp; spilling x159 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rbp; loading flag
adox rcx, rdi
adox r8, r10
adox r15, rbx
mulx rax, rdi, [ r11 + 0x10 ]; x156, x155<- x3 * arg2[2]
mov r10, 0x0 ; moving imm to reg
adcx rsi, r10
mulx rbx, r10, [ r11 + 0x8 ]; x158, x157<- x3 * arg2[1]
clc;
adcx r10, r12
adox rsi, r9
seto r12b; spill OF x151 to reg (r12)
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0x80 ]
movzx r9, r12b; x152, copying x151 here, cause x151 is needed in a reg for other than x152, namely all: , x152, size: 1
movzx r14, r14b
lea r9, [ r9 + r14 ]
mulx rdx, r14, [ r11 + 0x18 ]; x154, x153<- x3 * arg2[3]
adcx rdi, rbx
mov rbx, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rcx; x168, swapping with x154, which is currently in rdx
mulx r12, rbp, rbx; _, x178<- x168 * 0xd838091dd2253531
adox r10, r8
adox rdi, r15
mov r12, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r12; 0xfffffffefffffc2f, swapping with x168, which is currently in rdx
mulx r8, r15, rbp; x187, x186<- x178 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x88 ], rdi; spilling x172 to mem
mulx rbx, rdi, rbp; x183, x182<- x178 * 0xffffffffffffffff
adcx r14, rax
mov [ rsp + 0x90 ], r9; spilling x152 to mem
mulx rax, r9, rbp; x185, x184<- x178 * 0xffffffffffffffff
mov [ rsp + 0x98 ], r10; spilling x170 to mem
mulx rbp, r10, rbp; x181, x180<- x178 * 0xffffffffffffffff
mov rdx, 0x0 ; moving imm to reg
adcx rcx, rdx
clc;
adcx r9, r8
adcx rdi, rax
adcx r10, rbx
adcx rbp, rdx
clc;
adcx r15, r12
adox r14, rsi
mov r15, [ rsp + 0x98 ]; x197, copying x170 here, cause x170 is needed in a reg for other than x197, namely all: , x197--x198, size: 1
adcx r15, r9
mov rsi, [ rsp + 0x90 ]; x176, copying x152 here, cause x152 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adox rsi, rcx
mov r12, [ rsp + 0x88 ]; x199, copying x172 here, cause x172 is needed in a reg for other than x199, namely all: , x199--x200, size: 1
adcx r12, rdi
setc r8b; spill CF x200 to reg (r8)
seto bl; spill OF x177 to reg (rbx)
mov rax, r15; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
mov rcx, 0xfffffffefffffc2f ; moving imm to reg
sub rax, rcx
mov r9, r12; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x217, x208--x209, size: 2
mov rdi, 0xffffffffffffffff ; moving imm to reg
sbb r9, rdi
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r8, r8b
adox r8, rdx; loading flag
adox r14, r10
adox rbp, rsi
movzx r10, bl; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
mov rsi, 0x0 ; moving imm to reg
adox r10, rsi
mov rbx, r14; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
sbb rbx, rdi
mov r8, rbp; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x212--x213, x219, size: 2
sbb r8, rdi
sbb r10, 0x00000000
cmovc r9, r12; if CF, x217<- x199 (nzVar)
cmovc r8, rbp; if CF, x219<- x203 (nzVar)
cmovc rax, r15; if CF, x216<- x197 (nzVar)
cmovc rbx, r14; if CF, x218<- x201 (nzVar)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x18 ], r8; out1[3] = x219
mov [ r10 + 0x10 ], rbx; out1[2] = x218
mov [ r10 + 0x8 ], r9; out1[1] = x217
mov [ r10 + 0x0 ], rax; out1[0] = x216
mov rbx, [ rsp + 0xa0 ]; restoring from stack
mov rbp, [ rsp + 0xa8 ]; restoring from stack
mov r12, [ rsp + 0xb0 ]; restoring from stack
mov r13, [ rsp + 0xb8 ]; restoring from stack
mov r14, [ rsp + 0xc0 ]; restoring from stack
mov r15, [ rsp + 0xc8 ]; restoring from stack
add rsp, 0xd0 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 84.93, best 72.61386138613861, lastGood 74.87128712871286
; seed 4292899296502668 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 710542 ms / 60000 runs=> 11.842366666666667ms/run
; Time spent for assembling and measureing (initial batch_size=101, initial num_batches=101): 120045 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.16894849284067656
; number reverted permutation/ tried permutation: 25268 / 30235 =83.572%
; number reverted decision/ tried decision: 21049 / 29766 =70.715%