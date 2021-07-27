SECTION .text
	GLOBAL mul_secp256k1
mul_secp256k1:
sub rsp, 0xc8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x98 ], rbx; saving to stack
mov [ rsp + 0xa0 ], rbp; saving to stack
mov [ rsp + 0xa8 ], r12; saving to stack
mov [ rsp + 0xb0 ], r13; saving to stack
mov [ rsp + 0xb8 ], r14; saving to stack
mov [ rsp + 0xc0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, [ rsi + 0x10 ]; load m64 x2 to register64
xchg rdx, r10; x2, swapping with arg2, which is currently in rdx
mulx r11, rbx, [ r10 + 0x18 ]; x101, x100<- x2 * arg2[3]
mulx rbp, r12, [ r10 + 0x0 ]; x107, x106<- x2 * arg2[0]
mulx r13, r14, [ r10 + 0x10 ]; x103, x102<- x2 * arg2[2]
mov r15, [ rsi + 0x8 ]; load m64 x1 to register64
mulx rdx, rcx, [ r10 + 0x8 ]; x105, x104<- x2 * arg2[1]
xchg rdx, r15; x1, swapping with x105, which is currently in rdx
mulx r8, r9, [ r10 + 0x8 ]; x52, x51<- x1 * arg2[1]
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
xor rdi, rdi
adox rcx, rbp
adox r14, r15
adox rbx, r13
mov rbp, rdx; preserving value of x1 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r13, r15, rax; x12, x11<- x4 * arg2[0]
adox r11, rdi
mov rdi, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r15; x11 to rdx
mov [ rsp + 0x8 ], r11; spilling x114 to mem
mulx r15, r11, rdi; _, x20<- x11 * 0xd838091dd2253531
xchg rdx, rbp; x1, swapping with x11, which is currently in rdx
mulx r15, rdi, [ r10 + 0x10 ]; x50, x49<- x1 * arg2[2]
mov [ rsp + 0x10 ], rsi; spilling arg1 to mem
mov [ rsp + 0x18 ], rbx; spilling x112 to mem
mulx rsi, rbx, [ r10 + 0x0 ]; x54, x53<- x1 * arg2[0]
mov [ rsp + 0x20 ], r14; spilling x110 to mem
mulx rdx, r14, [ r10 + 0x18 ]; x48, x47<- x1 * arg2[3]
adcx r9, rsi
adcx rdi, r8
mov r8, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r11; x20, swapping with x48, which is currently in rdx
mov [ rsp + 0x28 ], rcx; spilling x108 to mem
mulx rsi, rcx, r8; x29, x28<- x20 * 0xfffffffefffffc2f
adcx r14, r15
mov r15, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x30 ], r12; spilling x106 to mem
mulx r8, r12, r15; x27, x26<- x20 * 0xffffffffffffffff
adc r11, 0x0
test al, al
adox rcx, rbp
mov rcx, rdx; preserving value of x20 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx rbp, r15, rax; x10, x9<- x4 * arg2[1]
mov rdx, rax; x4 to rdx
mov [ rsp + 0x38 ], r11; spilling x61 to mem
mulx rax, r11, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
adcx r15, r13
adcx r11, rbp
setc r13b; spill CF x16 to reg (r13)
clc;
adcx r12, rsi
adox r12, r15
setc sil; spill CF x31 to reg (rsi)
clc;
adcx rbx, r12
mov rbp, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rbx; x62, swapping with x4, which is currently in rdx
mulx r15, r12, rbp; _, x72<- x62 * 0xd838091dd2253531
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rcx; x20, swapping with x62, which is currently in rdx
mov [ rsp + 0x40 ], r14; spilling x59 to mem
mulx rbp, r14, r15; x25, x24<- x20 * 0xffffffffffffffff
xchg rdx, r15; 0xffffffffffffffff, swapping with x20, which is currently in rdx
mov [ rsp + 0x48 ], rdi; spilling x57 to mem
mov [ rsp + 0x50 ], rbp; spilling x25 to mem
mulx rdi, rbp, r12; x79, x78<- x72 * 0xffffffffffffffff
mov rdx, 0xfffffffefffffc2f ; moving imm to reg
mov [ rsp + 0x58 ], rdi; spilling x79 to mem
mov [ rsp + 0x60 ], r9; spilling x55 to mem
mulx rdi, r9, r12; x81, x80<- x72 * 0xfffffffefffffc2f
setc dl; spill CF x63 to reg (rdx)
clc;
adcx r9, rcx
setc r9b; spill CF x90 to reg (r9)
clc;
mov rcx, -0x1 ; moving imm to reg
movzx rsi, sil
adcx rsi, rcx; loading flag
adcx r8, r14
xchg rdx, rbx; x4, swapping with x63, which is currently in rdx
mulx rdx, rsi, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
setc r14b; spill CF x33 to reg (r14)
clc;
adcx rbp, rdi
setc dil; spill CF x83 to reg (rdi)
clc;
movzx r13, r13b
adcx r13, rcx; loading flag
adcx rax, rsi
adox r8, r11
seto r13b; spill OF x42 to reg (r13)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r11, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r11; loading flag
adox r8, [ rsp + 0x60 ]
adcx rdx, rcx
mov rbx, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; 0xffffffffffffffff, swapping with x19, which is currently in rdx
mulx r15, rsi, r15; x23, x22<- x20 * 0xffffffffffffffff
clc;
movzx r14, r14b
adcx r14, r11; loading flag
adcx rsi, [ rsp + 0x50 ]
adcx r15, rcx
clc;
movzx r13, r13b
adcx r13, r11; loading flag
adcx rax, rsi
adcx r15, rbx
mulx r14, r13, r12; x77, x76<- x72 * 0xffffffffffffffff
setc bl; spill CF x46 to reg (rbx)
clc;
movzx rdi, dil
adcx rdi, r11; loading flag
adcx r13, [ rsp + 0x58 ]
mulx r12, rdi, r12; x75, x74<- x72 * 0xffffffffffffffff
mov rsi, [ rsp + 0x48 ]; x66, copying x57 here, cause x57 is needed in a reg for other than x66, namely all: , x66--x67, size: 1
adox rsi, rax
adcx rdi, r14
mov rax, [ rsp + 0x40 ]; x68, copying x59 here, cause x59 is needed in a reg for other than x68, namely all: , x68--x69, size: 1
adox rax, r15
movzx rbx, bl
mov r15, [ rsp + 0x38 ]; x70, copying x61 here, cause x61 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adox r15, rbx
seto bl; spill OF x71 to reg (rbx)
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r9, r9b
adox r9, rcx; loading flag
adox r8, rbp
mov r11, 0x0 ; moving imm to reg
adcx r12, r11
adox r13, rsi
clc;
adcx r8, [ rsp + 0x30 ]
mov r9, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r9; 0xd838091dd2253531, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rbp, r14, r8; _, x125<- x115 * 0xd838091dd2253531
mov rbp, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r14; x125, swapping with 0xd838091dd2253531, which is currently in rdx
mulx rsi, r11, rbp; x134, x133<- x125 * 0xfffffffefffffc2f
adox rdi, rax
mulx rax, rcx, r9; x130, x129<- x125 * 0xffffffffffffffff
mov rbp, [ rsp + 0x28 ]; x117, copying x108 here, cause x108 is needed in a reg for other than x117, namely all: , x117--x118, size: 1
adcx rbp, r13
adox r12, r15
mov r15, [ rsp + 0x20 ]; x119, copying x110 here, cause x110 is needed in a reg for other than x119, namely all: , x119--x120, size: 1
adcx r15, rdi
mulx r13, rdi, r9; x128, x127<- x125 * 0xffffffffffffffff
mov r9, [ rsp + 0x18 ]; x121, copying x112 here, cause x112 is needed in a reg for other than x121, namely all: , x121--x122, size: 1
adcx r9, r12
movzx r12, bl; x99, copying x71 here, cause x71 is needed in a reg for other than x99, namely all: , x99, size: 1
mov r14, 0x0 ; moving imm to reg
adox r12, r14
mov rbx, 0xffffffffffffffff ; moving imm to reg
mulx rdx, r14, rbx; x132, x131<- x125 * 0xffffffffffffffff
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rsi
mov rsi, [ rsp + 0x8 ]; x123, copying x114 here, cause x114 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adcx rsi, r12
adox rcx, rdx
adox rdi, rax
setc al; spill CF x124 to reg (rax)
clc;
adcx r11, r8
mov r8, [ rsp + 0x10 ]; load m64 arg1 to register64
mov r11, [ r8 + 0x18 ]; load m64 x3 to register64
adcx r14, rbp
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rbp, r12, r11; x160, x159<- x3 * arg2[0]
adcx rcx, r15
adcx rdi, r9
mov r15, 0x0 ; moving imm to reg
adox r13, r15
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, r14
adcx r13, rsi
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rsi, r14, r11; x156, x155<- x3 * arg2[2]
mov r15, 0xd838091dd2253531 ; moving imm to reg
mov rdx, r12; x168 to rdx
mulx r12, r9, r15; _, x178<- x168 * 0xd838091dd2253531
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r9; x178, swapping with x168, which is currently in rdx
mulx rbx, r15, r12; x185, x184<- x178 * 0xffffffffffffffff
xchg rdx, r11; x3, swapping with x178, which is currently in rdx
mov [ rsp + 0x68 ], r13; spilling x150 to mem
mulx r12, r13, [ r10 + 0x18 ]; x154, x153<- x3 * arg2[3]
mov [ rsp + 0x70 ], r12; spilling x154 to mem
mov r12, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r11; x178, swapping with x3, which is currently in rdx
mov [ rsp + 0x78 ], r13; spilling x153 to mem
mov [ rsp + 0x80 ], rsi; spilling x156 to mem
mulx r13, rsi, r12; x187, x186<- x178 * 0xfffffffefffffc2f
movzx r12, al; x152, copying x124 here, cause x124 is needed in a reg for other than x152, namely all: , x152, size: 1
mov [ rsp + 0x88 ], rbx; spilling x185 to mem
mov rbx, 0x0 ; moving imm to reg
adcx r12, rbx
mov rax, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x90 ], r12; spilling x152 to mem
mulx rbx, r12, rax; x181, x180<- x178 * 0xffffffffffffffff
clc;
adcx rsi, r9
xchg rdx, r11; x3, swapping with x178, which is currently in rdx
mulx rdx, r9, [ r10 + 0x8 ]; x158, x157<- x3 * arg2[1]
setc al; spill CF x196 to reg (rax)
clc;
adcx r15, r13
setc r13b; spill CF x189 to reg (r13)
clc;
adcx r9, rbp
adox r9, rcx
adcx r14, rdx
adox r14, rdi
mov rbp, 0xffffffffffffffff ; moving imm to reg
mov rdx, rbp; 0xffffffffffffffff to rdx
mulx r11, rbp, r11; x183, x182<- x178 * 0xffffffffffffffff
seto cl; spill OF x173 to reg (rcx)
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, rdi; loading flag
adox rbp, [ rsp + 0x88 ]
adox r12, r11
mov r13, [ rsp + 0x80 ]; load m64 x156 to register64
mov r11, [ rsp + 0x78 ]; x165, copying x153 here, cause x153 is needed in a reg for other than x165, namely all: , x165--x166, size: 1
adcx r11, r13
mov r13, 0x0 ; moving imm to reg
adox rbx, r13
inc rdi; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r13; loading flag
adox r9, r15
mov rax, [ rsp + 0x70 ]; x167, copying x154 here, cause x154 is needed in a reg for other than x167, namely all: , x167, size: 1
adcx rax, rdi
clc;
movzx rcx, cl
adcx rcx, r13; loading flag
adcx r11, [ rsp + 0x68 ]
mov r15, [ rsp + 0x90 ]; x176, copying x152 here, cause x152 is needed in a reg for other than x176, namely all: , x176--x177, size: 1
adcx r15, rax
adox rbp, r14
adox r12, r11
adox rbx, r15
setc cl; spill CF x177 to reg (rcx)
seto r14b; spill OF x204 to reg (r14)
mov rax, r9; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x206--x207, x216, size: 2
mov r11, 0xfffffffefffffc2f ; moving imm to reg
sub rax, r11
mov r15, rbp; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
sbb r15, rdx
mov rdi, r12; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x210--x211, x218, size: 2
sbb rdi, rdx
mov r13, rbx; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb r13, rdx
movzx r11, r14b; x205, copying x204 here, cause x204 is needed in a reg for other than x205, namely all: , x205, size: 1
movzx rcx, cl
lea r11, [ r11 + rcx ]
sbb r11, 0x00000000
cmovc r15, rbp; if CF, x217<- x199 (nzVar)
cmovc r13, rbx; if CF, x219<- x203 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x18 ], r13; out1[3] = x219
cmovc rdi, r12; if CF, x218<- x201 (nzVar)
mov [ r11 + 0x8 ], r15; out1[1] = x217
cmovc rax, r9; if CF, x216<- x197 (nzVar)
mov [ r11 + 0x10 ], rdi; out1[2] = x218
mov [ r11 + 0x0 ], rax; out1[0] = x216
mov rbx, [ rsp + 0x98 ]; restoring from stack
mov rbp, [ rsp + 0xa0 ]; restoring from stack
mov r12, [ rsp + 0xa8 ]; restoring from stack
mov r13, [ rsp + 0xb0 ]; restoring from stack
mov r14, [ rsp + 0xb8 ]; restoring from stack
mov r15, [ rsp + 0xc0 ]; restoring from stack
add rsp, 0xc8 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 96.39, best 69.66666666666667, lastGood 72.51020408163265
; seed 2681584295662131 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 870353 ms / 60000 runs=> 14.505883333333333ms/run
; Time spent for assembling and measureing (initial batch_size=100, initial num_batches=101): 131924 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.1515752803747445
; number reverted permutation/ tried permutation: 25138 / 29868 =84.164%
; number reverted decision/ tried decision: 21838 / 30133 =72.472%