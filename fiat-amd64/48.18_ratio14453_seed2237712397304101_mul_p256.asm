SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0xa8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x78 ], rbx; saving to stack
mov [ rsp + 0x80 ], rbp; saving to stack
mov [ rsp + 0x88 ], r12; saving to stack
mov [ rsp + 0x90 ], r13; saving to stack
mov [ rsp + 0x98 ], r14; saving to stack
mov [ rsp + 0xa0 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, rbx, rax; x10, x9<- x4 * arg2[1]
mov rdx, rax; x4 to rdx
mulx rax, rbp, [ r10 + 0x18 ]; x6, x5<- x4 * arg2[3]
mulx r12, r13, [ r10 + 0x0 ]; x12, x11<- x4 * arg2[0]
mov r14, [ rsi + 0x10 ]; load m64 x2 to register64
xor r15, r15
adox rbx, r12
mov rcx, rdx; preserving value of x4 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mulx r8, r9, r14; x87, x86<- x2 * arg2[2]
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx rcx, r12, rcx; x8, x7<- x4 * arg2[2]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r15, rdi, r14; x89, x88<- x2 * arg2[1]
adox r12, r11
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x8 ], r12; spilling x15 to mem
mulx r11, r12, r14; x91, x90<- x2 * arg2[0]
adox rbp, rcx
mov rcx, 0x0 ; moving imm to reg
adox rax, rcx
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r14, rcx, r14; x85, x84<- x2 * arg2[3]
mov [ rsp + 0x10 ], rax; spilling x19 to mem
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rdi, r11
adcx r9, r15
mov r15, 0xffffffff ; moving imm to reg
mov rdx, r13; x11 to rdx
mulx r13, r11, r15; x23, x22<- x11 * 0xffffffff
adcx rcx, r8
mov r8, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x18 ], rcx; spilling x96 to mem
mulx r15, rcx, r8; x25, x24<- x11 * 0xffffffffffffffff
adc r14, 0x0
mov r8, rdx; preserving value of x11 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x20 ], r14; spilling x98 to mem
mov [ rsp + 0x28 ], r9; spilling x94 to mem
mulx r14, r9, rax; x46, x45<- x1 * arg2[0]
mov [ rsp + 0x30 ], rdi; spilling x92 to mem
xor rdi, rdi
adox rcx, r8
adcx r11, r15
adox r11, rbx
adcx r13, rdi
clc;
adcx r9, r11
mov rcx, [ rsp + 0x8 ]; x33, copying x15 here, cause x15 is needed in a reg for other than x33, namely all: , x33--x34, size: 1
adox rcx, r13
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; x54 to rdx
mulx r9, r15, rbx; x69, x68<- x54 * 0xffffffffffffffff
seto r11b; spill OF x34 to reg (r11)
mov r13, -0x3 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, rdx
mov r15, rdx; preserving value of x54 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx rdi, r13, rax; x44, x43<- x1 * arg2[1]
seto bl; spill OF x74 to reg (rbx)
mov [ rsp + 0x38 ], rbp; spilling x17 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r14
adcx r13, rcx
mov r14, 0xffffffff ; moving imm to reg
mov rdx, r14; 0xffffffff to rdx
mulx r14, rcx, r15; x67, x66<- x54 * 0xffffffff
setc bpl; spill CF x57 to reg (rbp)
clc;
adcx rcx, r9
setc r9b; spill CF x71 to reg (r9)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r13, rcx
setc bl; spill CF x76 to reg (rbx)
clc;
adcx r12, r13
mov rcx, 0xffffffff ; moving imm to reg
mov rdx, r12; x99 to rdx
mulx r12, r13, rcx; x112, x111<- x99 * 0xffffffff
mov rcx, 0xffffffffffffffff ; moving imm to reg
mov byte [ rsp + 0x40 ], bl; spilling byte x76 to mem
mov byte [ rsp + 0x48 ], bpl; spilling byte x57 to mem
mulx rbx, rbp, rcx; x114, x113<- x99 * 0xffffffffffffffff
setc cl; spill CF x100 to reg (rcx)
clc;
adcx r13, rbx
mov rbx, rdx; preserving value of x99 into a new reg
mov rdx, [ r10 + 0x10 ]; saving arg2[2] in rdx.
mov [ rsp + 0x50 ], r13; spilling x115 to mem
mov [ rsp + 0x58 ], rbp; spilling x113 to mem
mulx r13, rbp, rax; x42, x41<- x1 * arg2[2]
mov byte [ rsp + 0x60 ], cl; spilling byte x100 to mem
mov rcx, 0x0 ; moving imm to reg
adcx r12, rcx
mov rcx, 0xffffffff00000001 ; moving imm to reg
mov rdx, rcx; 0xffffffff00000001 to rdx
mulx r8, rcx, r8; x21, x20<- x11 * 0xffffffff00000001
adox rbp, rdi
clc;
mov rdi, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rdi; loading flag
adcx rcx, [ rsp + 0x38 ]
mulx r15, r11, r15; x65, x64<- x54 * 0xffffffff00000001
movzx rdi, r9b; x72, copying x71 here, cause x71 is needed in a reg for other than x72, namely all: , x72, size: 1
lea rdi, [ rdi + r14 ]
mov r14, [ rsp + 0x10 ]; x37, copying x19 here, cause x19 is needed in a reg for other than x37, namely all: , x37--x38, size: 1
adcx r14, r8
setc r9b; spill CF x38 to reg (r9)
movzx r8, byte [ rsp + 0x48 ]; load byte memx57 to register64
clc;
mov rdx, -0x1 ; moving imm to reg
adcx r8, rdx; loading flag
adcx rcx, rbp
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rax, r8, rax; x40, x39<- x1 * arg2[3]
adox r8, r13
mov r13, 0x0 ; moving imm to reg
adox rax, r13
adcx r8, r14
mov rbp, [ rsi + 0x18 ]; load m64 x3 to register64
movzx r14, byte [ rsp + 0x40 ]; load byte memx76 to register64
dec r13; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
adox r14, r13; loading flag
adox rcx, rdi
adox r11, r8
mov r14, 0xffffffff00000001 ; moving imm to reg
mov rdx, r14; 0xffffffff00000001 to rdx
mulx r14, rdi, rbx; x110, x109<- x99 * 0xffffffff00000001
movzx r8, r9b; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adcx r8, rax
adox r15, r8
setc r9b; spill CF x63 to reg (r9)
movzx rax, byte [ rsp + 0x60 ]; load byte memx100 to register64
clc;
adcx rax, r13; loading flag
adcx rcx, [ rsp + 0x30 ]
movzx rax, r9b; x83, copying x63 here, cause x63 is needed in a reg for other than x83, namely all: , x83, size: 1
mov r8, 0x0 ; moving imm to reg
adox rax, r8
mov r9, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, r13, rbp; x136, x135<- x3 * arg2[0]
mov r9, [ rsp + 0x28 ]; x103, copying x94 here, cause x94 is needed in a reg for other than x103, namely all: , x103--x104, size: 1
adcx r9, r11
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x58 ]
mov rbx, [ rsp + 0x18 ]; x105, copying x96 here, cause x96 is needed in a reg for other than x105, namely all: , x105--x106, size: 1
adcx rbx, r15
mov r15, [ rsp + 0x50 ]; x120, copying x115 here, cause x115 is needed in a reg for other than x120, namely all: , x120--x121, size: 1
adox r15, rcx
mov rcx, [ rsp + 0x20 ]; x107, copying x98 here, cause x98 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx rcx, rax
adox r12, r9
adox rdi, rbx
adox r14, rcx
seto al; spill OF x127 to reg (rax)
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, r15
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; x144 to rdx
mulx r13, rbx, r9; x159, x158<- x144 * 0xffffffffffffffff
movzx r15, al; x128, copying x127 here, cause x127 is needed in a reg for other than x128, namely all: , x128, size: 1
adcx r15, r11
mov rcx, 0xffffffff ; moving imm to reg
mulx rax, r11, rcx; x157, x156<- x144 * 0xffffffff
mov rcx, rdx; preserving value of x144 into a new reg
mov rdx, [ r10 + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x68 ], r15; spilling x128 to mem
mulx r9, r15, rbp; x130, x129<- x3 * arg2[3]
mov rdx, rbp; x3 to rdx
mov [ rsp + 0x70 ], r14; spilling x126 to mem
mulx rbp, r14, [ r10 + 0x10 ]; x132, x131<- x3 * arg2[2]
clc;
adcx rbx, rcx
setc bl; spill CF x164 to reg (rbx)
clc;
adcx r11, r13
mov r13, 0x0 ; moving imm to reg
adcx rax, r13
mulx rdx, r13, [ r10 + 0x8 ]; x134, x133<- x3 * arg2[1]
clc;
adcx r13, r8
adcx r14, rdx
adox r13, r12
adcx r15, rbp
mov r8, 0x0 ; moving imm to reg
adcx r9, r8
clc;
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, r12; loading flag
adcx r13, r11
adox r14, rdi
mov rdi, 0xffffffff00000001 ; moving imm to reg
mov rdx, rdi; 0xffffffff00000001 to rdx
mulx rcx, rbp, rcx; x155, x154<- x144 * 0xffffffff00000001
adcx rax, r14
mov rbx, [ rsp + 0x70 ]; x150, copying x126 here, cause x126 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adox rbx, r15
adcx rbp, rbx
mov r11, [ rsp + 0x68 ]; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox r11, r9
adcx rcx, r11
seto r15b; spill OF x173 to reg (r15)
adc r15b, 0x0
movzx r15, r15b
mov r9, r13; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x184, x174--x175, size: 2
mov r14, 0xffffffffffffffff ; moving imm to reg
sub r9, r14
mov rbx, rax; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
mov r11, 0xffffffff ; moving imm to reg
sbb rbx, r11
mov r12, rbp; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r12, 0x00000000
mov r8, rcx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x180--x181, x187, size: 2
sbb r8, rdx
movzx rdx, r15b; _, copying x173 here, cause x173 is needed in a reg for other than _, namely all: , _--x183, size: 1
sbb rdx, 0x00000000
cmovc rbx, rax; if CF, x185<- x167 (nzVar)
cmovc r9, r13; if CF, x184<- x165 (nzVar)
mov r13, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r13 + 0x0 ], r9; out1[0] = x184
cmovc r12, rbp; if CF, x186<- x169 (nzVar)
cmovc r8, rcx; if CF, x187<- x171 (nzVar)
mov [ r13 + 0x8 ], rbx; out1[1] = x185
mov [ r13 + 0x10 ], r12; out1[2] = x186
mov [ r13 + 0x18 ], r8; out1[3] = x187
mov rbx, [ rsp + 0x78 ]; restoring from stack
mov rbp, [ rsp + 0x80 ]; restoring from stack
mov r12, [ rsp + 0x88 ]; restoring from stack
mov r13, [ rsp + 0x90 ]; restoring from stack
mov r14, [ rsp + 0x98 ]; restoring from stack
mov r15, [ rsp + 0xa0 ]; restoring from stack
add rsp, 0xa8 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 59.34, best 47.44055944055944, lastGood 48.18181818181818
; seed 2237712397304101 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 600890 ms / 60000 runs=> 10.014833333333334ms/run
; Time spent for assembling and measureing (initial batch_size=143, initial num_batches=101): 152252 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2533774900564163
; number reverted permutation/ tried permutation: 22990 / 29833 =77.062%
; number reverted decision/ tried decision: 24609 / 30168 =81.573%