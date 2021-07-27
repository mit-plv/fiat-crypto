SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0x80 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x50 ], rbx; saving to stack
mov [ rsp + 0x58 ], rbp; saving to stack
mov [ rsp + 0x60 ], r12; saving to stack
mov [ rsp + 0x68 ], r13; saving to stack
mov [ rsp + 0x70 ], r14; saving to stack
mov [ rsp + 0x78 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, rbx, rax; x10, x9<- x4 * arg2[1]
mov rdx, rax; x4 to rdx
mulx rax, rbp, [ r10 + 0x0 ]; x12, x11<- x4 * arg2[0]
mulx r12, r13, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
mulx rdx, r14, [ r10 + 0x10 ]; x8, x7<- x4 * arg2[2]
xor r15, r15
adox rbx, rax
adox r14, r11
adox r13, rdx
mov rcx, 0xffffffff ; moving imm to reg
mov rdx, rbp; x11 to rdx
mulx rbp, r8, rcx; x23, x22<- x11 * 0xffffffff
adox r12, r15
mov r9, 0xffffffffffffffff ; moving imm to reg
mulx r11, rax, r9; x25, x24<- x11 * 0xffffffffffffffff
adcx r8, r11
mov r11, [ rsi + 0x8 ]; load m64 x1 to register64
adc rbp, 0x0
add rax, rdx; could be done better, if r0 has been u8 as well
adcx r8, rbx
mov rax, rdx; preserving value of x11 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rbx, r15, r11; x46, x45<- x1 * arg2[0]
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r8
adcx rbp, r14
mov r14, 0xffffffffffffffff ; moving imm to reg
mov rdx, r14; 0xffffffffffffffff to rdx
mulx r14, r8, r15; x69, x68<- x54 * 0xffffffffffffffff
mov r9, [ rsi + 0x10 ]; load m64 x2 to register64
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx rax, rcx, rax; x21, x20<- x11 * 0xffffffff00000001
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r9; spilling x2 to mem
mulx rdi, r9, r15; x67, x66<- x54 * 0xffffffff
mov [ rsp + 0x10 ], rax; spilling x21 to mem
mov rax, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x18 ], r12; spilling x19 to mem
mov [ rsp + 0x20 ], rcx; spilling x20 to mem
mulx r12, rcx, r11; x44, x43<- x1 * arg2[1]
setc al; spill CF x34 to reg (rax)
clc;
adcx r9, r14
mov r14, 0x0 ; moving imm to reg
adcx rdi, r14
mov rdx, r11; x1 to rdx
mulx r11, r14, [ r10 + 0x10 ]; x42, x41<- x1 * arg2[2]
clc;
adcx rcx, rbx
mulx rdx, rbx, [ r10 + 0x18 ]; x40, x39<- x1 * arg2[3]
adox rcx, rbp
adcx r14, r12
adcx rbx, r11
seto bpl; spill OF x57 to reg (rbp)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r15
setc r8b; spill CF x52 to reg (r8)
clc;
movzx rax, al
adcx rax, r12; loading flag
adcx r13, [ rsp + 0x20 ]
adox r9, rcx
mov rax, [ rsp + 0x10 ]; load m64 x21 to register64
mov r11, [ rsp + 0x18 ]; x37, copying x19 here, cause x19 is needed in a reg for other than x37, namely all: , x37--x38, size: 1
adcx r11, rax
movzx rax, r8b; x53, copying x52 here, cause x52 is needed in a reg for other than x53, namely all: , x53, size: 1
lea rax, [ rax + rdx ]
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx r15, rcx, r15; x65, x64<- x54 * 0xffffffff00000001
setc r8b; spill CF x38 to reg (r8)
clc;
movzx rbp, bpl
adcx rbp, r12; loading flag
adcx r13, r14
adcx rbx, r11
movzx rbp, r8b; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adcx rbp, rax
adox rdi, r13
adox rcx, rbx
adox r15, rbp
seto r14b; spill OF x83 to reg (r14)
adc r14b, 0x0
movzx r14, r14b
mov r8, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r11, rax, [ rsp + 0x8 ]; x91, x90<- x2 * arg2[0]
adox rax, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, rax; x99 to rdx
mulx rax, r13, r9; x114, x113<- x99 * 0xffffffffffffffff
mov rbx, 0xffffffff ; moving imm to reg
mulx rbp, r12, rbx; x112, x111<- x99 * 0xffffffff
mov rbx, rdx; preserving value of x99 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r8, r9, [ rsp + 0x8 ]; x89, x88<- x2 * arg2[1]
adcx r12, rax
mov rax, 0x0 ; moving imm to reg
adcx rbp, rax
clc;
adcx r13, rbx
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r13, rax, [ rsp + 0x8 ]; x87, x86<- x2 * arg2[2]
mov byte [ rsp + 0x28 ], r14b; spilling byte x83 to mem
mov r14, [ rsi + 0x18 ]; load m64 x3 to register64
mov [ rsp + 0x30 ], r15; spilling x81 to mem
setc r15b; spill CF x119 to reg (r15)
clc;
adcx r9, r11
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x38 ], r13; spilling x87 to mem
mulx r11, r13, r14; x134, x133<- x3 * arg2[1]
adox r9, rdi
adcx rax, r8
adox rax, rcx
seto dil; spill OF x104 to reg (rdi)
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rcx; loading flag
adox r9, r12
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx r8, r12, r14; x136, x135<- x3 * arg2[0]
adox rbp, rax
setc r15b; spill CF x95 to reg (r15)
clc;
adcx r13, r8
setc al; spill CF x138 to reg (rax)
clc;
adcx r12, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x144 to rdx
mulx r12, r8, r9; x159, x158<- x144 * 0xffffffffffffffff
adcx r13, rbp
mov rbp, 0xffffffff ; moving imm to reg
mulx rcx, r9, rbp; x157, x156<- x144 * 0xffffffff
setc bpl; spill CF x147 to reg (rbp)
clc;
adcx r9, r12
mov r12, 0x0 ; moving imm to reg
adcx rcx, r12
mov r12, rdx; preserving value of x144 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x40 ], rcx; spilling x162 to mem
mov byte [ rsp + 0x48 ], bpl; spilling byte x147 to mem
mulx rcx, rbp, [ rsp + 0x8 ]; x85, x84<- x2 * arg2[3]
clc;
adcx r8, r12
adcx r9, r13
setc r8b; spill CF x166 to reg (r8)
clc;
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r13; loading flag
adcx rbp, [ rsp + 0x38 ]
mov r15, 0xffffffff00000001 ; moving imm to reg
mov rdx, r15; 0xffffffff00000001 to rdx
mulx rbx, r15, rbx; x110, x109<- x99 * 0xffffffff00000001
mov r13, 0x0 ; moving imm to reg
adcx rcx, r13
mulx r12, r13, r12; x155, x154<- x144 * 0xffffffff00000001
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, rdx; loading flag
adcx rbp, [ rsp + 0x30 ]
adox r15, rbp
mov rdx, r14; x3 to rdx
mulx r14, rdi, [ r10 + 0x10 ]; x132, x131<- x3 * arg2[2]
movzx rbp, byte [ rsp + 0x28 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx rbp, rcx
adox rbx, rbp
seto cl; spill OF x128 to reg (rcx)
adc cl, 0x0
movzx rcx, cl
mulx rdx, rbp, [ r10 + 0x18 ]; x130, x129<- x3 * arg2[3]
add al, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto al; since that has deps, resore it whereever it was
adox r11, rdi
movzx rax, byte [ rsp + 0x48 ]; load byte memx147 to register64
mov rdi, -0x1 ; moving imm to reg
adcx rax, rdi; loading flag
adcx r15, r11
adox rbp, r14
mov rax, 0x0 ; moving imm to reg
adox rdx, rax
adcx rbp, rbx
dec rax; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r8, r8b
adox r8, rax; loading flag
adox r15, [ rsp + 0x40 ]
movzx r8, cl; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adcx r8, rdx
adox r13, rbp
adox r12, r8
seto r14b; spill OF x173 to reg (r14)
adc r14b, 0x0
movzx r14, r14b
mov rbx, r9; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, x184, size: 2
mov rcx, 0xffffffffffffffff ; moving imm to reg
sub rbx, rcx
mov r11, r15; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov rdx, 0xffffffff ; moving imm to reg
sbb r11, rdx
mov rbp, r13; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb rbp, 0x00000000
mov r8, r12; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
mov rax, 0xffffffff00000001 ; moving imm to reg
sbb r8, rax
movzx rdx, r14b; _, copying x173 here, cause x173 is needed in a reg for other than _, namely all: , _--x183, size: 1
sbb rdx, 0x00000000
cmovc r8, r12; if CF, x187<- x171 (nzVar)
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x18 ], r8; out1[3] = x187
cmovc r11, r15; if CF, x185<- x167 (nzVar)
mov [ r12 + 0x8 ], r11; out1[1] = x185
cmovc rbp, r13; if CF, x186<- x169 (nzVar)
mov [ r12 + 0x10 ], rbp; out1[2] = x186
cmovc rbx, r9; if CF, x184<- x165 (nzVar)
mov [ r12 + 0x0 ], rbx; out1[0] = x184
mov rbx, [ rsp + 0x50 ]; restoring from stack
mov rbp, [ rsp + 0x58 ]; restoring from stack
mov r12, [ rsp + 0x60 ]; restoring from stack
mov r13, [ rsp + 0x68 ]; restoring from stack
mov r14, [ rsp + 0x70 ]; restoring from stack
mov r15, [ rsp + 0x78 ]; restoring from stack
add rsp, 0x80 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4799 MHz
; first cyclecount 81.05, best 63.67857142857143, lastGood 63.88181818181818
; seed 3975821006667828 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 656452 ms / 60000 runs=> 10.940866666666667ms/run
; Time spent for assembling and measureing (initial batch_size=112, initial num_batches=101): 124326 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.18939084655085214
; number reverted permutation/ tried permutation: 22223 / 29906 =74.310%
; number reverted decision/ tried decision: 23073 / 30095 =76.667%