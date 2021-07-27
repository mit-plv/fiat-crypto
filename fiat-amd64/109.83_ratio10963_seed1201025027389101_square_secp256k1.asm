SECTION .text
	GLOBAL square_secp256k1
square_secp256k1:
sub rsp, 0x88 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x58 ], rbx; saving to stack
mov [ rsp + 0x60 ], rbp; saving to stack
mov [ rsp + 0x68 ], r12; saving to stack
mov [ rsp + 0x70 ], r13; saving to stack
mov [ rsp + 0x78 ], r14; saving to stack
mov [ rsp + 0x80 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x4 to rdx
mulx rax, r10, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mulx r11, rbx, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
mulx rbp, r12, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
mulx rdx, r13, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
mov r14, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, r14; 0xd838091dd2253531, swapping with x8, which is currently in rdx
mulx r15, rcx, r10; _, x20<- x11 * 0xd838091dd2253531
test al, al
adox rbx, rax
adox r13, r11
mov r15, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rcx; x20, swapping with 0xd838091dd2253531, which is currently in rdx
mulx r8, r9, r15; x29, x28<- x20 * 0xfffffffefffffc2f
mov rax, 0xffffffffffffffff ; moving imm to reg
mulx r11, r15, rax; x27, x26<- x20 * 0xffffffffffffffff
adox r12, r14
mov r14, [ rsi + 0x8 ]; load m64 x1 to register64
adcx r15, r8
mov r8, 0x0 ; moving imm to reg
adox rbp, r8
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, r10
adox r15, rbx
xchg rdx, r14; x1, swapping with x20, which is currently in rdx
mulx r9, r10, [ rsi + 0x0 ]; x54, x53<- x1 * arg1[0]
seto bl; spill OF x40 to reg (rbx)
mov rax, -0x3 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, r15
mulx r15, r8, [ rsi + 0x8 ]; x52, x51<- x1 * arg1[1]
xchg rdx, rcx; 0xd838091dd2253531, swapping with x1, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rax, rdi, r10; _, x72<- x62 * 0xd838091dd2253531
mov rax, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, rax; 0xfffffffefffffc2f, swapping with 0xd838091dd2253531, which is currently in rdx
mov [ rsp + 0x8 ], rbp; spilling x19 to mem
mulx rax, rbp, rdi; x81, x80<- x72 * 0xfffffffefffffc2f
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x10 ], r15; spilling x52 to mem
mov [ rsp + 0x18 ], r12; spilling x17 to mem
mulx r15, r12, r14; x25, x24<- x20 * 0xffffffffffffffff
adcx r12, r11
seto r11b; spill OF x63 to reg (r11)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rdx; loading flag
adox r13, r12
seto bl; spill OF x42 to reg (rbx)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r10
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r14; x20, swapping with 0x0, which is currently in rdx
mulx rdx, r10, rbp; x23, x22<- x20 * 0xffffffffffffffff
xchg rdx, rbp; 0xffffffffffffffff, swapping with x23, which is currently in rdx
mulx r12, r14, rdi; x79, x78<- x72 * 0xffffffffffffffff
seto dl; spill OF x90 to reg (rdx)
mov [ rsp + 0x20 ], r12; spilling x79 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rax
adcx r10, r15
xchg rdx, rcx; x1, swapping with x90, which is currently in rdx
mulx rax, r15, [ rsi + 0x10 ]; x50, x49<- x1 * arg1[2]
seto r12b; spill OF x83 to reg (r12)
mov [ rsp + 0x28 ], rax; spilling x50 to mem
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r9
setc r9b; spill CF x35 to reg (r9)
clc;
movzx r11, r11b
adcx r11, rax; loading flag
adcx r13, r8
setc r11b; spill CF x65 to reg (r11)
clc;
movzx rcx, cl
adcx rcx, rax; loading flag
adcx r13, r14
setc cl; spill CF x92 to reg (rcx)
clc;
movzx rbx, bl
adcx rbx, rax; loading flag
adcx r10, [ rsp + 0x18 ]
movzx rbx, r9b; x36, copying x35 here, cause x35 is needed in a reg for other than x36, namely all: , x36, size: 1
lea rbx, [ rbx + rbp ]
mov rbp, [ rsp + 0x10 ]; x57, copying x52 here, cause x52 is needed in a reg for other than x57, namely all: , x57--x58, size: 1
adox rbp, r15
seto r14b; spill OF x58 to reg (r14)
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r9; loading flag
adox r10, rbp
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx r8, r11, rdi; x77, x76<- x72 * 0xffffffffffffffff
xchg rdx, r15; x1, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x18 ]; x48, x47<- x1 * arg1[3]
mov rax, [ rsp + 0x8 ]; x45, copying x19 here, cause x19 is needed in a reg for other than x45, namely all: , x45--x46, size: 1
adcx rax, rbx
xchg rdx, rdi; x72, swapping with x48, which is currently in rdx
mulx rdx, rbx, r15; x75, x74<- x72 * 0xffffffffffffffff
setc r9b; spill CF x46 to reg (r9)
clc;
mov r15, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r15; loading flag
adcx rbp, [ rsp + 0x28 ]
mov r14, 0x0 ; moving imm to reg
adcx rdi, r14
adox rbp, rax
clc;
movzx r12, r12b
adcx r12, r15; loading flag
adcx r11, [ rsp + 0x20 ]
adcx rbx, r8
setc r12b; spill CF x87 to reg (r12)
clc;
movzx rcx, cl
adcx rcx, r15; loading flag
adcx r10, r11
adcx rbx, rbp
movzx rcx, r12b; x88, copying x87 here, cause x87 is needed in a reg for other than x88, namely all: , x88, size: 1
lea rcx, [ rcx + rdx ]
movzx r8, r9b; x70, copying x46 here, cause x46 is needed in a reg for other than x70, namely all: , x70--x71, size: 1
adox r8, rdi
mov r9, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, r9; x2 to rdx
mulx r9, rax, [ rsi + 0x0 ]; x107, x106<- x2 * arg1[0]
adcx rcx, r8
setc dil; spill CF x98 to reg (rdi)
clc;
adcx rax, r13
mov r13, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rax; x115, swapping with x2, which is currently in rdx
mulx rbp, r11, r13; _, x125<- x115 * 0xd838091dd2253531
movzx rbp, dil; x99, copying x98 here, cause x98 is needed in a reg for other than x99, namely all: , x99, size: 1
adox rbp, r14
xchg rdx, rax; x2, swapping with x115, which is currently in rdx
mulx r12, r8, [ rsi + 0x10 ]; x103, x102<- x2 * arg1[2]
mov rdi, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r11; x125, swapping with x2, which is currently in rdx
mulx r14, r15, rdi; x134, x133<- x125 * 0xfffffffefffffc2f
xchg rdx, r11; x2, swapping with x125, which is currently in rdx
mulx rdi, r13, [ rsi + 0x8 ]; x105, x104<- x2 * arg1[1]
mov [ rsp + 0x30 ], rbp; spilling x99 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rax
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx rax, rbp, r11; x132, x131<- x125 * 0xffffffffffffffff
seto dl; spill OF x143 to reg (rdx)
mov [ rsp + 0x38 ], rcx; spilling x97 to mem
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r9
adox r8, rdi
seto r9b; spill OF x111 to reg (r9)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r14
xchg rdx, r15; x2, swapping with x143, which is currently in rdx
mulx rdx, r14, [ rsi + 0x18 ]; x101, x100<- x2 * arg1[3]
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x101, which is currently in rdx
mov [ rsp + 0x40 ], rbp; spilling x135 to mem
mulx rcx, rbp, r11; x130, x129<- x125 * 0xffffffffffffffff
adcx r13, r10
adox rbp, rax
adcx r8, rbx
seto r10b; spill OF x138 to reg (r10)
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
movzx r9, r9b
adox r9, rax; loading flag
adox r12, r14
mulx r11, r9, r11; x128, x127<- x125 * 0xffffffffffffffff
adox rdi, rbx
inc rax; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rbx; loading flag
adox r13, [ rsp + 0x40 ]
mov r15, [ rsp + 0x38 ]; x121, copying x97 here, cause x97 is needed in a reg for other than x121, namely all: , x121--x122, size: 1
adcx r15, r12
mov r14, [ rsp + 0x30 ]; x123, copying x99 here, cause x99 is needed in a reg for other than x123, namely all: , x123--x124, size: 1
adcx r14, rdi
mov r12, [ rsi + 0x18 ]; load m64 x3 to register64
setc dil; spill CF x124 to reg (rdi)
clc;
movzx r10, r10b
adcx r10, rbx; loading flag
adcx rcx, r9
mov r10, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, rax, r12; x160, x159<- x3 * arg1[0]
adox rbp, r8
mov rdx, 0x0 ; moving imm to reg
adcx r11, rdx
clc;
adcx rax, r13
adox rcx, r15
mov r8, 0xd838091dd2253531 ; moving imm to reg
xchg rdx, rax; x168, swapping with 0x0, which is currently in rdx
mulx r13, r15, r8; _, x178<- x168 * 0xd838091dd2253531
adox r11, r14
mov r13, 0xfffffffefffffc2f ; moving imm to reg
xchg rdx, r13; 0xfffffffefffffc2f, swapping with x168, which is currently in rdx
mulx r14, rax, r15; x187, x186<- x178 * 0xfffffffefffffc2f
mov rbx, rdx; preserving value of 0xfffffffefffffc2f into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, r10, r12; x158, x157<- x3 * arg1[1]
seto dl; spill OF x151 to reg (rdx)
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x178, swapping with x151, which is currently in rdx
mov [ rsp + 0x48 ], r11; spilling x150 to mem
mulx rbx, r11, r9; x185, x184<- x178 * 0xffffffffffffffff
adcx r10, rbp
mov [ rsp + 0x50 ], rcx; spilling x148 to mem
mulx rbp, rcx, r9; x183, x182<- x178 * 0xffffffffffffffff
movzx r9, r15b; x152, copying x151 here, cause x151 is needed in a reg for other than x152, namely all: , x152, size: 1
movzx rdi, dil
lea r9, [ r9 + rdi ]
seto dil; spill OF x162 to reg (rdi)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r13
mov rax, rdx; preserving value of x178 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r13, r15, r12; x156, x155<- x3 * arg1[2]
setc dl; spill CF x171 to reg (rdx)
clc;
adcx r11, r14
adcx rcx, rbx
setc r14b; spill CF x191 to reg (r14)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rbx; loading flag
adcx r8, r15
xchg rdx, r12; x3, swapping with x171, which is currently in rdx
mulx rdx, rdi, [ rsi + 0x18 ]; x154, x153<- x3 * arg1[3]
adox r11, r10
adcx rdi, r13
setc r10b; spill CF x166 to reg (r10)
clc;
movzx r12, r12b
adcx r12, rbx; loading flag
adcx r8, [ rsp + 0x50 ]
adox rcx, r8
setc r12b; spill CF x173 to reg (r12)
seto r13b; spill OF x200 to reg (r13)
mov r15, r11; x206, copying x197 here, cause x197 is needed in a reg for other than x206, namely all: , x216, x206--x207, size: 2
mov r8, 0xfffffffefffffc2f ; moving imm to reg
sub r15, r8
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbx; loading flag
adox rdi, [ rsp + 0x48 ]
seto r12b; spill OF x175 to reg (r12)
mov rbx, rcx; x208, copying x199 here, cause x199 is needed in a reg for other than x208, namely all: , x208--x209, x217, size: 2
mov r8, 0xffffffffffffffff ; moving imm to reg
sbb rbx, r8
movzx r8, r10b; x167, copying x166 here, cause x166 is needed in a reg for other than x167, namely all: , x167, size: 1
lea r8, [ r8 + rdx ]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx rax, r10, rax; x181, x180<- x178 * 0xffffffffffffffff
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rdx; loading flag
adox r9, r8
setc r12b; spill CF x209 to reg (r12)
clc;
movzx r14, r14b
adcx r14, rdx; loading flag
adcx rbp, r10
seto r14b; spill OF x177 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r8; loading flag
adox rdi, rbp
adcx rax, rdx
adox rax, r9
movzx r13, r14b; x205, copying x177 here, cause x177 is needed in a reg for other than x205, namely all: , x205, size: 1
adox r13, rdx
movzx r10, r12b; x209, copying x209 here, cause x209 is needed in a reg for other than x209, namely all: , x210--x211, size: 1
add r10, -0x1
mov r10, rdi; x210, copying x201 here, cause x201 is needed in a reg for other than x210, namely all: , x218, x210--x211, size: 2
mov r12, 0xffffffffffffffff ; moving imm to reg
sbb r10, r12
mov r9, rax; x212, copying x203 here, cause x203 is needed in a reg for other than x212, namely all: , x219, x212--x213, size: 2
sbb r9, r12
sbb r13, 0x00000000
cmovc r9, rax; if CF, x219<- x203 (nzVar)
cmovc r15, r11; if CF, x216<- x197 (nzVar)
cmovc rbx, rcx; if CF, x217<- x199 (nzVar)
cmovc r10, rdi; if CF, x218<- x201 (nzVar)
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x8 ], rbx; out1[1] = x217
mov [ r13 + 0x18 ], r9; out1[3] = x219
mov [ r13 + 0x10 ], r10; out1[2] = x218
mov [ r13 + 0x0 ], r15; out1[0] = x216
mov rbx, [ rsp + 0x58 ]; restoring from stack
mov rbp, [ rsp + 0x60 ]; restoring from stack
mov r12, [ rsp + 0x68 ]; restoring from stack
mov r13, [ rsp + 0x70 ]; restoring from stack
mov r14, [ rsp + 0x78 ]; restoring from stack
mov r15, [ rsp + 0x80 ]; restoring from stack
add rsp, 0x88 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 129.77, best 103.55, lastGood 109.82926829268293
; seed 1201025027389101 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1067037 ms / 60000 runs=> 17.78395ms/run
; Time spent for assembling and measureing (initial batch_size=81, initial num_batches=101): 186092 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.17440070025687957
; number reverted permutation/ tried permutation: 27060 / 30012 =90.164%
; number reverted decision/ tried decision: 21668 / 29989 =72.253%