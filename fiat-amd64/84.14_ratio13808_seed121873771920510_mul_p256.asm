SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0x98 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x68 ], rbx; saving to stack
mov [ rsp + 0x70 ], rbp; saving to stack
mov [ rsp + 0x78 ], r12; saving to stack
mov [ rsp + 0x80 ], r13; saving to stack
mov [ rsp + 0x88 ], r14; saving to stack
mov [ rsp + 0x90 ], r15; saving to stack
mov rax, [ rsi + 0x18 ]; load m64 x3 to register64
mov r10, [ rsi + 0x8 ]; load m64 x1 to register64
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rbp, rax; x136, x135<- x3 * arg2[0]
mov rdx, rax; x3 to rdx
mulx rax, r12, [ r11 + 0x10 ]; x132, x131<- x3 * arg2[2]
mulx r13, r14, [ r11 + 0x8 ]; x134, x133<- x3 * arg2[1]
mov r15, [ rsi + 0x0 ]; load m64 x4 to register64
mov rcx, rdx; preserving value of x3 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, r9, r15; x12, x11<- x4 * arg2[0]
add r14, rbx; could be done better, if r0 has been u8 as well
adcx r12, r13
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; x11 to rdx
mulx r9, r13, rbx; x25, x24<- x11 * 0xffffffffffffffff
xchg rdx, rcx; x3, swapping with x11, which is currently in rdx
mulx rdx, rbx, [ r11 + 0x18 ]; x130, x129<- x3 * arg2[3]
adcx rbx, rax
adc rdx, 0x0
mov rax, rdx; preserving value of x143 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rbx; spilling x141 to mem
mulx rdi, rbx, r10; x46, x45<- x1 * arg2[0]
mov rdx, r15; x4 to rdx
mov [ rsp + 0x10 ], rax; spilling x143 to mem
mulx r15, rax, [ r11 + 0x8 ]; x10, x9<- x4 * arg2[1]
mov [ rsp + 0x18 ], r12; spilling x139 to mem
mov r12, 0xffffffff ; moving imm to reg
xchg rdx, r12; 0xffffffff, swapping with x4, which is currently in rdx
mov [ rsp + 0x20 ], r14; spilling x137 to mem
mov [ rsp + 0x28 ], rbp; spilling x135 to mem
mulx r14, rbp, rcx; x23, x22<- x11 * 0xffffffff
add rbp, r9; could be done better, if r0 has been u8 as well
adc r14, 0x0
add r13, rcx; could be done better, if r0 has been u8 as well
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r8
adcx rbp, rax
setc r8b; spill CF x32 to reg (r8)
clc;
adcx rbx, rbp
mov r9, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rbx; x54, swapping with 0xffffffff, which is currently in rdx
mulx rax, rbp, r9; x69, x68<- x54 * 0xffffffffffffffff
mulx r13, r9, rbx; x67, x66<- x54 * 0xffffffff
setc bl; spill CF x55 to reg (rbx)
clc;
adcx r9, rax
xchg rdx, r12; x4, swapping with x54, which is currently in rdx
mov [ rsp + 0x30 ], rsi; spilling arg1 to mem
mulx rax, rsi, [ r11 + 0x10 ]; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x38 ], rax; spilling x8 to mem
mov rax, 0x0 ; moving imm to reg
adcx r13, rax
adox rsi, r15
mov r15, rdx; preserving value of x4 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x40 ], r13; spilling x72 to mem
mulx rax, r13, r10; x44, x43<- x1 * arg2[1]
mov rdx, r15; x4 to rdx
mulx rdx, r15, [ r11 + 0x18 ]; x6, x5<- x4 * arg2[3]
clc;
mov [ rsp + 0x48 ], rdx; spilling x6 to mem
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx rsi, r14
seto r14b; spill OF x16 to reg (r14)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, rdi
seto dil; spill OF x48 to reg (rdi)
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rbx, bl
adox rbx, rdx; loading flag
adox rsi, r13
mov r8, 0xffffffff00000001 ; moving imm to reg
mov rdx, r8; 0xffffffff00000001 to rdx
mulx rcx, r8, rcx; x21, x20<- x11 * 0xffffffff00000001
setc bl; spill CF x34 to reg (rbx)
clc;
adcx rbp, r12
adcx r9, rsi
xchg rdx, r10; x1, swapping with 0xffffffff00000001, which is currently in rdx
mulx rbp, r13, [ r11 + 0x10 ]; x42, x41<- x1 * arg2[2]
seto sil; spill OF x57 to reg (rsi)
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, r10; loading flag
adox rax, r13
setc dil; spill CF x76 to reg (rdi)
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx r15, [ rsp + 0x38 ]
mulx rdx, r14, [ r11 + 0x18 ]; x40, x39<- x1 * arg2[3]
mov r13, [ rsp + 0x48 ]; x19, copying x6 here, cause x6 is needed in a reg for other than x19, namely all: , x19, size: 1
mov r10, 0x0 ; moving imm to reg
adcx r13, r10
adox r14, rbp
adox rdx, r10
add bl, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc bl; since that has deps, resore it whereever it was
adcx r15, r8
mov rbx, 0xffffffff00000001 ; moving imm to reg
xchg rdx, rbx; 0xffffffff00000001, swapping with x53, which is currently in rdx
mulx r12, r8, r12; x65, x64<- x54 * 0xffffffff00000001
adcx rcx, r13
mov rbp, [ rsp + 0x30 ]; load m64 arg1 to register64
mov r13, [ rbp + 0x10 ]; load m64 x2 to register64
mov r10, -0x1 ; moving imm to reg
movzx rsi, sil
adox rsi, r10; loading flag
adox r15, rax
setc sil; spill CF x38 to reg (rsi)
clc;
movzx rdi, dil
adcx rdi, r10; loading flag
adcx r15, [ rsp + 0x40 ]
adox r14, rcx
adcx r8, r14
movzx rdi, sil; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox rdi, rbx
mov rax, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, rsi, r13; x91, x90<- x2 * arg2[0]
seto cl; spill OF x63 to reg (rcx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rsi, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, rsi; x99 to rdx
mulx r14, r10, r9; x114, x113<- x99 * 0xffffffffffffffff
adcx r12, rdi
mov rdi, rdx; preserving value of x99 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx rax, r9, r13; x89, x88<- x2 * arg2[1]
mov [ rsp + 0x50 ], r12; spilling x81 to mem
movzx r12, cl; x83, copying x63 here, cause x63 is needed in a reg for other than x83, namely all: , x83, size: 1
mov [ rsp + 0x58 ], r8; spilling x79 to mem
mov r8, 0x0 ; moving imm to reg
adcx r12, r8
clc;
adcx r9, rbx
adox r9, r15
mov rdx, r13; x2 to rdx
mulx r13, r15, [ r11 + 0x10 ]; x87, x86<- x2 * arg2[2]
mov rcx, 0xffffffff ; moving imm to reg
xchg rdx, rdi; x99, swapping with x2, which is currently in rdx
mulx rbx, r8, rcx; x112, x111<- x99 * 0xffffffff
adcx r15, rax
seto al; spill OF x102 to reg (rax)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r14
mov r14, 0xffffffff00000001 ; moving imm to reg
mov [ rsp + 0x60 ], r12; spilling x83 to mem
mulx rcx, r12, r14; x110, x109<- x99 * 0xffffffff00000001
mov r14, 0x0 ; moving imm to reg
adox rbx, r14
xchg rdx, rdi; x2, swapping with x99, which is currently in rdx
mulx rdx, r14, [ r11 + 0x18 ]; x85, x84<- x2 * arg2[3]
adcx r14, r13
adc rdx, 0x0
xor r13, r13
adox r10, rdi
mov r10, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, r10; loading flag
adcx r15, [ rsp + 0x58 ]
mov rdi, [ rsp + 0x50 ]; x105, copying x81 here, cause x81 is needed in a reg for other than x105, namely all: , x105--x106, size: 1
adcx rdi, r14
adox r8, r9
mov rax, [ rsp + 0x60 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx rax, rdx
setc r9b; spill CF x108 to reg (r9)
clc;
adcx r8, [ rsp + 0x28 ]
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r8; x144 to rdx
mulx r8, r13, r14; x159, x158<- x144 * 0xffffffffffffffff
adox rbx, r15
adox r12, rdi
adox rcx, rax
movzx r15, r9b; x128, copying x108 here, cause x108 is needed in a reg for other than x128, namely all: , x128, size: 1
mov rdi, 0x0 ; moving imm to reg
adox r15, rdi
mov r9, [ rsp + 0x20 ]; x146, copying x137 here, cause x137 is needed in a reg for other than x146, namely all: , x146--x147, size: 1
adcx r9, rbx
mov rax, 0xffffffff ; moving imm to reg
mulx rbx, rdi, rax; x157, x156<- x144 * 0xffffffff
mov r10, [ rsp + 0x18 ]; x148, copying x139 here, cause x139 is needed in a reg for other than x148, namely all: , x148--x149, size: 1
adcx r10, r12
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r8
mov r8, 0x0 ; moving imm to reg
adox rbx, r8
mov r8, [ rsp + 0x8 ]; x150, copying x141 here, cause x141 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adcx r8, rcx
mov rcx, 0xffffffff00000001 ; moving imm to reg
mulx r12, rax, rcx; x155, x154<- x144 * 0xffffffff00000001
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rdx
adox rdi, r9
mov r13, [ rsp + 0x10 ]; x152, copying x143 here, cause x143 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adcx r13, r15
adox rbx, r10
adox rax, r8
adox r12, r13
setc dl; spill CF x153 to reg (rdx)
seto r15b; spill OF x172 to reg (r15)
mov r9, rdi; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
mov r10, 0xffffffffffffffff ; moving imm to reg
sub r9, r10
mov r8, rbx; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
mov r13, 0xffffffff ; moving imm to reg
sbb r8, r13
mov r14, rax; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178--x179, x186, size: 2
sbb r14, 0x00000000
movzx r13, r15b; x173, copying x172 here, cause x172 is needed in a reg for other than x173, namely all: , x173, size: 1
movzx rdx, dl
lea r13, [ r13 + rdx ]
mov rdx, r12; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x180--x181, x187, size: 2
sbb rdx, rcx
sbb r13, 0x00000000
cmovc r9, rdi; if CF, x184<- x165 (nzVar)
cmovc r14, rax; if CF, x186<- x169 (nzVar)
cmovc rdx, r12; if CF, x187<- x171 (nzVar)
cmovc r8, rbx; if CF, x185<- x167 (nzVar)
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x8 ], r8; out1[1] = x185
mov [ r13 + 0x0 ], r9; out1[0] = x184
mov [ r13 + 0x18 ], rdx; out1[3] = x187
mov [ r13 + 0x10 ], r14; out1[2] = x186
mov rbx, [ rsp + 0x68 ]; restoring from stack
mov rbp, [ rsp + 0x70 ]; restoring from stack
mov r12, [ rsp + 0x78 ]; restoring from stack
mov r13, [ rsp + 0x80 ]; restoring from stack
mov r14, [ rsp + 0x88 ]; restoring from stack
mov r15, [ rsp + 0x90 ]; restoring from stack
add rsp, 0x98 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2117 MHz
; first cyclecount 96.52, best 80.97619047619048, lastGood 84.14285714285714
; seed 121873771920510 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 948186 ms / 60000 runs=> 15.8031ms/run
; Time spent for assembling and measureing (initial batch_size=85, initial num_batches=101): 201669 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2126892824825509
; number reverted permutation/ tried permutation: 26899 / 30144 =89.235%
; number reverted decision/ tried decision: 22741 / 29857 =76.166%