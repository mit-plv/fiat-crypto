SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0x68 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x38 ], rbx; saving to stack
mov [ rsp + 0x40 ], rbp; saving to stack
mov [ rsp + 0x48 ], r12; saving to stack
mov [ rsp + 0x50 ], r13; saving to stack
mov [ rsp + 0x58 ], r14; saving to stack
mov [ rsp + 0x60 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rbx, rax; x12, x11<- x4 * arg2[0]
mov rbp, [ rsi + 0x8 ]; load m64 x1 to register64
mov r12, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; 0xffffffffffffffff to rdx
mulx r12, r13, rbx; x25, x24<- x11 * 0xffffffffffffffff
mov r14, 0xffffffff ; moving imm to reg
xchg rdx, rbx; x11, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r15, rcx, r14; x23, x22<- x11 * 0xffffffff
test al, al
adox r13, rdx
mov r13, rdx; preserving value of x11 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r8, r9, rax; x10, x9<- x4 * arg2[1]
adcx rcx, r12
setc r12b; spill CF x27 to reg (r12)
clc;
adcx r9, r11
adox rcx, r9
mov rdx, rbp; x1 to rdx
mulx rbp, r11, [ r10 + 0x0 ]; x46, x45<- x1 * arg2[0]
seto r9b; spill OF x32 to reg (r9)
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rcx
xchg rdx, rbx; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx rcx, r14, r11; x69, x68<- x54 * 0xffffffffffffffff
xchg rdx, rax; x4, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rax, rdi, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x8 ], rsi; spilling arg1 to mem
movzx rsi, r12b; x28, copying x27 here, cause x27 is needed in a reg for other than x28, namely all: , x28, size: 1
lea rsi, [ rsi + r15 ]
adcx rdi, r8
setc r15b; spill CF x16 to reg (r15)
clc;
adcx r14, r11
setc r14b; spill CF x74 to reg (r14)
clc;
mov r8, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r8; loading flag
adcx rdi, rsi
mov r12, 0xffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffff, swapping with x4, which is currently in rdx
mulx r9, rsi, r11; x67, x66<- x54 * 0xffffffff
xchg rdx, rbx; x1, swapping with 0xffffffff, which is currently in rdx
mulx r8, rbx, [ r10 + 0x8 ]; x44, x43<- x1 * arg2[1]
xchg rdx, r12; x4, swapping with x1, which is currently in rdx
mov [ rsp + 0x10 ], r8; spilling x44 to mem
mulx rdx, r8, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
mov [ rsp + 0x18 ], rdx; spilling x6 to mem
setc dl; spill CF x34 to reg (rdx)
clc;
adcx rbx, rbp
adox rbx, rdi
setc bpl; spill CF x48 to reg (rbp)
clc;
adcx rsi, rcx
seto cl; spill OF x57 to reg (rcx)
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rdi; loading flag
adox rbx, rsi
mov r14, 0x0 ; moving imm to reg
adcx r9, r14
clc;
movzx r15, r15b
adcx r15, rdi; loading flag
adcx rax, r8
mov r15, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r13; x11, swapping with x34, which is currently in rdx
mulx rdx, r8, r15; x21, x20<- x11 * 0xffffffff00000001
setc sil; spill CF x18 to reg (rsi)
clc;
movzx r13, r13b
adcx r13, rdi; loading flag
adcx rax, r8
xchg rdx, r12; x1, swapping with x21, which is currently in rdx
mulx r13, r8, [ r10 + 0x10 ]; x42, x41<- x1 * arg2[2]
setc r14b; spill CF x36 to reg (r14)
clc;
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r8, [ rsp + 0x10 ]
setc bpl; spill CF x50 to reg (rbp)
clc;
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx rax, r8
movzx rcx, sil; x19, copying x18 here, cause x18 is needed in a reg for other than x19, namely all: , x19, size: 1
mov r8, [ rsp + 0x18 ]; load m64 x6 to register64
lea rcx, [ rcx + r8 ]; r8/64 + m8
mulx rdx, r8, [ r10 + 0x18 ]; x40, x39<- x1 * arg2[3]
adox r9, rax
setc sil; spill CF x59 to reg (rsi)
clc;
movzx r14, r14b
adcx r14, rdi; loading flag
adcx rcx, r12
mov r12, [ rsp + 0x8 ]; load m64 arg1 to register64
mov r14, [ r12 + 0x10 ]; load m64 x2 to register64
setc al; spill CF x38 to reg (rax)
clc;
movzx rbp, bpl
adcx rbp, rdi; loading flag
adcx r13, r8
mov rbp, 0x0 ; moving imm to reg
adcx rdx, rbp
xchg rdx, r11; x54, swapping with x53, which is currently in rdx
mulx rdx, r8, r15; x65, x64<- x54 * 0xffffffff00000001
clc;
movzx rsi, sil
adcx rsi, rdi; loading flag
adcx rcx, r13
adox r8, rcx
xchg rdx, r14; x2, swapping with x65, which is currently in rdx
mulx rsi, r13, [ r10 + 0x0 ]; x91, x90<- x2 * arg2[0]
movzx rcx, al; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adcx rcx, r11
adox r14, rcx
seto al; spill OF x82 to reg (rax)
mov r11, -0x3 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r13, rbx
movzx rbx, al; x83, copying x82 here, cause x82 is needed in a reg for other than x83, namely all: , x83, size: 1
adcx rbx, rbp
mulx rcx, rax, [ r10 + 0x8 ]; x89, x88<- x2 * arg2[1]
clc;
adcx rax, rsi
mulx rsi, rbp, [ r10 + 0x10 ]; x87, x86<- x2 * arg2[2]
mov r11, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mulx rdi, r15, r13; x114, x113<- x99 * 0xffffffffffffffff
adox rax, r9
mov r9, 0xffffffff ; moving imm to reg
xchg rdx, r9; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mov [ rsp + 0x20 ], rbx; spilling x83 to mem
mulx r9, rbx, r13; x112, x111<- x99 * 0xffffffff
setc dl; spill CF x93 to reg (rdx)
clc;
adcx rbx, rdi
mov rdi, 0x0 ; moving imm to reg
adcx r9, rdi
clc;
adcx r15, r13
xchg rdx, r11; x2, swapping with x93, which is currently in rdx
mulx rdx, r15, [ r10 + 0x18 ]; x85, x84<- x2 * arg2[3]
adcx rbx, rax
setc al; spill CF x121 to reg (rax)
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rdi; loading flag
adcx rcx, rbp
mov r11, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r13; x99, swapping with x85, which is currently in rdx
mulx rdx, rbp, r11; x110, x109<- x99 * 0xffffffff00000001
adcx r15, rsi
adox rcx, r8
adox r15, r14
setc r8b; spill CF x97 to reg (r8)
clc;
movzx rax, al
adcx rax, rdi; loading flag
adcx rcx, r9
movzx r14, r8b; x98, copying x97 here, cause x97 is needed in a reg for other than x98, namely all: , x98, size: 1
lea r14, [ r14 + r13 ]
adcx rbp, r15
mov rsi, [ rsp + 0x20 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adox rsi, r14
mov r9, [ r12 + 0x18 ]; load m64 x3 to register64
xchg rdx, r9; x3, swapping with x110, which is currently in rdx
mulx r13, rax, [ r10 + 0x0 ]; x136, x135<- x3 * arg2[0]
adcx r9, rsi
seto r8b; spill OF x108 to reg (r8)
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, rbx
movzx rbx, r8b; x128, copying x108 here, cause x108 is needed in a reg for other than x128, namely all: , x128, size: 1
adcx rbx, rdi
mov r15, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mulx r14, r8, rax; x159, x158<- x144 * 0xffffffffffffffff
mov rsi, 0xffffffff ; moving imm to reg
xchg rdx, rax; x144, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rdi, rax, rsi; x157, x156<- x144 * 0xffffffff
xchg rdx, r15; x3, swapping with x144, which is currently in rdx
mulx rsi, r11, [ r10 + 0x8 ]; x134, x133<- x3 * arg2[1]
clc;
adcx r8, r15
setc r8b; spill CF x164 to reg (r8)
clc;
adcx rax, r14
mov [ rsp + 0x28 ], rbx; spilling x128 to mem
mulx r14, rbx, [ r10 + 0x18 ]; x130, x129<- x3 * arg2[3]
mov [ rsp + 0x30 ], r9; spilling x126 to mem
mov r9, 0x0 ; moving imm to reg
adcx rdi, r9
mulx rdx, r9, [ r10 + 0x10 ]; x132, x131<- x3 * arg2[2]
clc;
adcx r11, r13
adcx r9, rsi
adcx rbx, rdx
mov r13, 0x0 ; moving imm to reg
adcx r14, r13
adox r11, rcx
clc;
mov rcx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rcx; loading flag
adcx r11, rax
adox r9, rbp
adcx rdi, r9
setc bpl; spill CF x168 to reg (rbp)
seto sil; spill OF x149 to reg (rsi)
mov r8, r11; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, x184, size: 2
mov rax, 0xffffffffffffffff ; moving imm to reg
sub r8, rax
mov rdx, rdi; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov r9, 0xffffffff ; moving imm to reg
sbb rdx, r9
inc rcx; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r13; loading flag
adox rbx, [ rsp + 0x30 ]
mov rsi, 0xffffffff00000001 ; moving imm to reg
xchg rdx, r15; x144, swapping with x176, which is currently in rdx
mulx rdx, rcx, rsi; x155, x154<- x144 * 0xffffffff00000001
mov r13, [ rsp + 0x28 ]; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox r13, r14
seto r14b; spill OF x153 to reg (r14)
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r9; loading flag
adox rbx, rcx
adox rdx, r13
movzx rbp, r14b; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
mov rcx, 0x0 ; moving imm to reg
adox rbp, rcx
mov r14, rbx; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178--x179, x186, size: 2
sbb r14, 0x00000000
mov r13, rdx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x180--x181, x187, size: 2
sbb r13, rsi
sbb rbp, 0x00000000
cmovc r8, r11; if CF, x184<- x165 (nzVar)
cmovc r14, rbx; if CF, x186<- x169 (nzVar)
cmovc r15, rdi; if CF, x185<- x167 (nzVar)
mov rbp, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbp + 0x0 ], r8; out1[0] = x184
cmovc r13, rdx; if CF, x187<- x171 (nzVar)
mov [ rbp + 0x10 ], r14; out1[2] = x186
mov [ rbp + 0x8 ], r15; out1[1] = x185
mov [ rbp + 0x18 ], r13; out1[3] = x187
mov rbx, [ rsp + 0x38 ]; restoring from stack
mov rbp, [ rsp + 0x40 ]; restoring from stack
mov r12, [ rsp + 0x48 ]; restoring from stack
mov r13, [ rsp + 0x50 ]; restoring from stack
mov r14, [ rsp + 0x58 ]; restoring from stack
mov r15, [ rsp + 0x60 ]; restoring from stack
add rsp, 0x68 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 79.04, best 60.37096774193548, lastGood 60.552845528455286
; seed 202417025616803 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 579974 ms / 60000 runs=> 9.666233333333333ms/run
; Time spent for assembling and measureing (initial batch_size=123, initial num_batches=101): 148428 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2559218171849083
; number reverted permutation/ tried permutation: 26386 / 30173 =87.449%
; number reverted decision/ tried decision: 22071 / 29828 =73.994%