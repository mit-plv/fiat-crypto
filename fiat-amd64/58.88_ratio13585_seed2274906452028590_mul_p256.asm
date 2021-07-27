SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0xb0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x80 ], rbx; saving to stack
mov [ rsp + 0x88 ], rbp; saving to stack
mov [ rsp + 0x90 ], r12; saving to stack
mov [ rsp + 0x98 ], r13; saving to stack
mov [ rsp + 0xa0 ], r14; saving to stack
mov [ rsp + 0xa8 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
xchg rdx, rax; x4, swapping with arg2, which is currently in rdx
mulx r10, r11, [ rax + 0x8 ]; x10, x9<- x4 * arg2[1]
mulx rbx, rbp, [ rax + 0x0 ]; x12, x11<- x4 * arg2[0]
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffffffffffff, swapping with x4, which is currently in rdx
mulx r13, r14, rbp; x25, x24<- x11 * 0xffffffffffffffff
mov r15, 0xffffffff ; moving imm to reg
xchg rdx, rbp; x11, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rcx, r8, r15; x23, x22<- x11 * 0xffffffff
test al, al
adox r8, r13
adcx r14, rdx
mov r14, [ rsi + 0x8 ]; load m64 x1 to register64
seto r9b; spill OF x27 to reg (r9)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rbx
adcx r8, r11
mov rbx, [ rsi + 0x10 ]; load m64 x2 to register64
xchg rdx, r14; x1, swapping with x11, which is currently in rdx
mulx r11, r13, [ rax + 0x0 ]; x46, x45<- x1 * arg2[0]
seto bpl; spill OF x14 to reg (rbp)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r8
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffff, swapping with x1, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r15, rdi, r13; x67, x66<- x54 * 0xffffffff
mov rdx, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x8 ], r11; spilling x46 to mem
mov [ rsp + 0x10 ], r10; spilling x10 to mem
mulx r11, r10, r13; x69, x68<- x54 * 0xffffffffffffffff
setc dl; spill CF x32 to reg (rdx)
clc;
adcx rdi, r11
mov r11, 0x0 ; moving imm to reg
adcx r15, r11
xchg rdx, rbx; x2, swapping with x32, which is currently in rdx
mov [ rsp + 0x18 ], r15; spilling x72 to mem
mulx r11, r15, [ rax + 0x8 ]; x89, x88<- x2 * arg2[1]
mov [ rsp + 0x20 ], r14; spilling x11 to mem
mov [ rsp + 0x28 ], rdi; spilling x70 to mem
mulx r14, rdi, [ rax + 0x0 ]; x91, x90<- x2 * arg2[0]
clc;
adcx r15, r14
mov [ rsp + 0x30 ], r15; spilling x92 to mem
mulx r14, r15, [ rax + 0x10 ]; x87, x86<- x2 * arg2[2]
mov [ rsp + 0x38 ], rdi; spilling x90 to mem
mulx rdx, rdi, [ rax + 0x18 ]; x85, x84<- x2 * arg2[3]
adcx r15, r11
mov r11, rdx; preserving value of x85 into a new reg
mov rdx, [ rax + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x40 ], r15; spilling x94 to mem
mov byte [ rsp + 0x48 ], bl; spilling byte x32 to mem
mulx r15, rbx, r12; x8, x7<- x4 * arg2[2]
adcx rdi, r14
mov r14, 0x0 ; moving imm to reg
adcx r11, r14
movzx r14, r9b; x28, copying x27 here, cause x27 is needed in a reg for other than x28, namely all: , x28, size: 1
lea r14, [ r14 + rcx ]
clc;
adcx r10, r13
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r10, rcx, r8; x44, x43<- x1 * arg2[1]
setc r9b; spill CF x74 to reg (r9)
clc;
mov [ rsp + 0x50 ], rsi; spilling arg1 to mem
mov rsi, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, rsi; loading flag
adcx rbx, [ rsp + 0x10 ]
setc bpl; spill CF x16 to reg (rbp)
movzx rsi, byte [ rsp + 0x48 ]; load byte memx32 to register64
clc;
mov [ rsp + 0x58 ], r11; spilling x98 to mem
mov r11, -0x1 ; moving imm to reg
adcx rsi, r11; loading flag
adcx rbx, r14
setc sil; spill CF x34 to reg (rsi)
clc;
adcx rcx, [ rsp + 0x8 ]
mov rdx, r8; x1 to rdx
mulx r8, r14, [ rax + 0x10 ]; x42, x41<- x1 * arg2[2]
xchg rdx, r12; x4, swapping with x1, which is currently in rdx
mulx rdx, r11, [ rax + 0x18 ]; x6, x5<- x4 * arg2[3]
adox rcx, rbx
seto bl; spill OF x57 to reg (rbx)
mov [ rsp + 0x60 ], rdi; spilling x96 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rdi; loading flag
adox rcx, [ rsp + 0x28 ]
adcx r14, r10
seto r9b; spill OF x76 to reg (r9)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r10; loading flag
adox r15, r11
adox rdx, rdi
mov rbp, 0xffffffff00000001 ; moving imm to reg
mov r11, rdx; preserving value of x19 into a new reg
mov rdx, [ rsp + 0x20 ]; saving x11 in rdx.
mulx rdx, rdi, rbp; x21, x20<- x11 * 0xffffffff00000001
mov r10, rdx; preserving value of x21 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mulx r12, rbp, r12; x40, x39<- x1 * arg2[3]
mov [ rsp + 0x68 ], rcx; spilling x75 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rsi, sil
adox rsi, rcx; loading flag
adox r15, rdi
adcx rbp, r8
setc sil; spill CF x52 to reg (rsi)
clc;
movzx rbx, bl
adcx rbx, rcx; loading flag
adcx r15, r14
movzx r8, sil; x53, copying x52 here, cause x52 is needed in a reg for other than x53, namely all: , x53, size: 1
lea r8, [ r8 + r12 ]
adox r10, r11
mov rbx, 0xffffffff00000001 ; moving imm to reg
mov rdx, rbx; 0xffffffff00000001 to rdx
mulx r13, rbx, r13; x65, x64<- x54 * 0xffffffff00000001
adcx rbp, r10
setc r14b; spill CF x61 to reg (r14)
clc;
movzx r9, r9b
adcx r9, rcx; loading flag
adcx r15, [ rsp + 0x18 ]
movzx r9, r14b; x62, copying x61 here, cause x61 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox r9, r8
mov r11, [ rsp + 0x68 ]; load m64 x75 to register64
seto dil; spill OF x63 to reg (rdi)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0x38 ]
mov r12, [ rsp + 0x30 ]; x101, copying x92 here, cause x92 is needed in a reg for other than x101, namely all: , x101--x102, size: 1
adox r12, r15
adcx rbx, rbp
mov rsi, [ rsp + 0x40 ]; x103, copying x94 here, cause x94 is needed in a reg for other than x103, namely all: , x103--x104, size: 1
adox rsi, rbx
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r11; x99, swapping with 0xffffffff00000001, which is currently in rdx
mulx r10, r14, r8; x112, x111<- x99 * 0xffffffff
adcx r13, r9
mov rbp, 0xffffffffffffffff ; moving imm to reg
mulx r15, r9, rbp; x114, x113<- x99 * 0xffffffffffffffff
movzx rbx, dil; x83, copying x63 here, cause x63 is needed in a reg for other than x83, namely all: , x83, size: 1
adcx rbx, rcx
clc;
adcx r14, r15
mov rdi, [ rsp + 0x60 ]; x105, copying x96 here, cause x96 is needed in a reg for other than x105, namely all: , x105--x106, size: 1
adox rdi, r13
adcx r10, rcx
clc;
adcx r9, rdx
mov r9, [ rsp + 0x58 ]; x107, copying x98 here, cause x98 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adox r9, rbx
mov r13, [ rsp + 0x50 ]; load m64 arg1 to register64
mov r15, [ r13 + 0x18 ]; load m64 x3 to register64
adcx r14, r12
mulx rdx, r12, r11; x110, x109<- x99 * 0xffffffff00000001
xchg rdx, r15; x3, swapping with x110, which is currently in rdx
mulx rbx, rcx, [ rax + 0x0 ]; x136, x135<- x3 * arg2[0]
adcx r10, rsi
seto sil; spill OF x108 to reg (rsi)
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r14
adcx r12, rdi
xchg rdx, r8; 0xffffffff, swapping with x3, which is currently in rdx
mulx rdi, r14, rcx; x157, x156<- x144 * 0xffffffff
mov rbp, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffffffffffff, swapping with 0xffffffff, which is currently in rdx
mulx rbp, r11, rcx; x159, x158<- x144 * 0xffffffffffffffff
adcx r15, r9
xchg rdx, r8; x3, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r9, r8, [ rax + 0x10 ]; x132, x131<- x3 * arg2[2]
mov [ rsp + 0x70 ], r15; spilling x126 to mem
movzx r15, sil; x128, copying x108 here, cause x108 is needed in a reg for other than x128, namely all: , x128, size: 1
mov [ rsp + 0x78 ], r9; spilling x132 to mem
mov r9, 0x0 ; moving imm to reg
adcx r15, r9
clc;
adcx r14, rbp
adcx rdi, r9
mulx rsi, rbp, [ rax + 0x8 ]; x134, x133<- x3 * arg2[1]
clc;
adcx rbp, rbx
adcx r8, rsi
adox rbp, r10
adox r8, r12
seto bl; spill OF x149 to reg (rbx)
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, rcx
mulx rdx, r11, [ rax + 0x18 ]; x130, x129<- x3 * arg2[3]
adox r14, rbp
adox rdi, r8
mov r12, [ rsp + 0x78 ]; x141, copying x132 here, cause x132 is needed in a reg for other than x141, namely all: , x141--x142, size: 1
adcx r12, r11
setc sil; spill CF x142 to reg (rsi)
seto bpl; spill OF x168 to reg (rbp)
mov r8, r14; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
mov r11, 0xffffffffffffffff ; moving imm to reg
sub r8, r11
dec r9; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbx, bl
adox rbx, r9; loading flag
adox r12, [ rsp + 0x70 ]
seto bl; spill OF x151 to reg (rbx)
mov r9, rdi; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov r10, 0xffffffff ; moving imm to reg
sbb r9, r10
mov r11, 0xffffffff00000001 ; moving imm to reg
xchg rdx, rcx; x144, swapping with x130, which is currently in rdx
mulx rdx, r10, r11; x155, x154<- x144 * 0xffffffff00000001
movzx r11, sil; x143, copying x142 here, cause x142 is needed in a reg for other than x143, namely all: , x143, size: 1
lea r11, [ r11 + rcx ]
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rcx; loading flag
adox r15, r11
seto sil; spill OF x153 to reg (rsi)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rbx; loading flag
adox r12, r10
adox rdx, r15
movzx rbp, sil; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
adox rbp, rcx
mov r10, r12; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r10, 0x00000000
mov r11, rdx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
mov r15, 0xffffffff00000001 ; moving imm to reg
sbb r11, r15
sbb rbp, 0x00000000
cmovc r10, r12; if CF, x186<- x169 (nzVar)
cmovc r8, r14; if CF, x184<- x165 (nzVar)
cmovc r11, rdx; if CF, x187<- x171 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x0 ], r8; out1[0] = x184
cmovc r9, rdi; if CF, x185<- x167 (nzVar)
mov [ rbp + 0x8 ], r9; out1[1] = x185
mov [ rbp + 0x18 ], r11; out1[3] = x187
mov [ rbp + 0x10 ], r10; out1[2] = x186
mov rbx, [ rsp + 0x80 ]; restoring from stack
mov rbp, [ rsp + 0x88 ]; restoring from stack
mov r12, [ rsp + 0x90 ]; restoring from stack
mov r13, [ rsp + 0x98 ]; restoring from stack
mov r14, [ rsp + 0xa0 ]; restoring from stack
mov r15, [ rsp + 0xa8 ]; restoring from stack
add rsp, 0xb0 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 78.88, best 56.95, lastGood 58.8780487804878
; seed 2274906452028590 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 770130 ms / 60000 runs=> 12.8355ms/run
; Time spent for assembling and measureing (initial batch_size=124, initial num_batches=101): 171003 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2220443301780219
; number reverted permutation/ tried permutation: 26188 / 29871 =87.670%
; number reverted decision/ tried decision: 23126 / 30130 =76.754%