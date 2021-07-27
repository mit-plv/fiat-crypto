SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0x80 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x50 ], rbx; saving to stack
mov [ rsp + 0x58 ], rbp; saving to stack
mov [ rsp + 0x60 ], r12; saving to stack
mov [ rsp + 0x68 ], r13; saving to stack
mov [ rsp + 0x70 ], r14; saving to stack
mov [ rsp + 0x78 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, rax; x4 to rdx
mulx rax, r10, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
mulx r11, rbx, [ rsi + 0x0 ]; x12, x11<- x4 * arg1[0]
mulx rbp, r12, [ rsi + 0x8 ]; x10, x9<- x4 * arg1[1]
add r12, r11; could be done better, if r0 has been u8 as well
mulx rdx, r13, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
adcx r13, rbp
mov r14, [ rsi + 0x8 ]; load m64 x1 to register64
adcx r10, rdx
mov r15, 0xffffffff ; moving imm to reg
mov rdx, rbx; x11 to rdx
mulx rbx, rcx, r15; x23, x22<- x11 * 0xffffffff
adc rax, 0x0
mov r8, 0xffffffffffffffff ; moving imm to reg
mulx r9, r11, r8; x25, x24<- x11 * 0xffffffffffffffff
xor rbp, rbp
adox rcx, r9
adox rbx, rbp
adcx r11, rdx
mov r11, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, rbp, r14; x46, x45<- x1 * arg1[0]
adcx rcx, r12
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rcx
adcx rbx, r13
mov rdx, r8; 0xffffffffffffffff to rdx
mulx r8, r12, rbp; x69, x68<- x54 * 0xffffffffffffffff
mov r13, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r15, r14; x44, x43<- x1 * arg1[1]
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r13, rdi, rbp; x67, x66<- x54 * 0xffffffff
mov rdx, [ rsi + 0x10 ]; load m64 x2 to register64
mov [ rsp + 0x8 ], rcx; spilling x44 to mem
setc cl; spill CF x34 to reg (rcx)
clc;
adcx r15, r9
adox r15, rbx
setc r9b; spill CF x48 to reg (r9)
clc;
adcx rdi, r8
setc bl; spill CF x71 to reg (rbx)
clc;
adcx r12, rbp
mulx r12, r8, [ rsi + 0x0 ]; x91, x90<- x2 * arg1[0]
adcx rdi, r15
setc r15b; spill CF x76 to reg (r15)
clc;
adcx r8, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x2, which is currently in rdx
mov byte [ rsp + 0x10 ], r15b; spilling byte x76 to mem
mov [ rsp + 0x18 ], r12; spilling x91 to mem
mulx r15, r12, r8; x114, x113<- x99 * 0xffffffffffffffff
mov rdx, 0xffffffff00000001 ; moving imm to reg
mov [ rsp + 0x20 ], r15; spilling x114 to mem
mulx r11, r15, r11; x21, x20<- x11 * 0xffffffff00000001
setc dl; spill CF x100 to reg (rdx)
clc;
mov [ rsp + 0x28 ], r12; spilling x113 to mem
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r12; loading flag
adcx r10, r15
adcx r11, rax
mov al, dl; preserving value of x100 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rcx, r15, rdi; x89, x88<- x2 * arg1[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x30 ], rcx; spilling x89 to mem
mulx r12, rcx, r14; x42, x41<- x1 * arg1[2]
movzx rdx, bl; x72, copying x71 here, cause x71 is needed in a reg for other than x72, namely all: , x72, size: 1
lea rdx, [ rdx + r13 ]
setc r13b; spill CF x38 to reg (r13)
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rbx; loading flag
adcx rcx, [ rsp + 0x8 ]
adox rcx, r10
seto r9b; spill OF x59 to reg (r9)
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x18 ]
seto r10b; spill OF x93 to reg (r10)
movzx rbx, byte [ rsp + 0x10 ]; load byte memx76 to register64
mov byte [ rsp + 0x38 ], r13b; spilling byte x38 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r13; loading flag
adox rcx, rdx
seto bl; spill OF x78 to reg (rbx)
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rdx; loading flag
adox rcx, r15
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, rax, r14; x40, x39<- x1 * arg1[3]
mov rdx, r8; _, copying x99 here, cause x99 is needed in a reg for other than _, namely all: , _--x119, x111--x112, x109--x110, size: 3
seto r15b; spill OF x102 to reg (r15)
mov byte [ rsp + 0x40 ], r10b; spilling byte x93 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rdx, [ rsp + 0x28 ]
adcx rax, r12
mov rdx, 0xffffffff ; moving imm to reg
mulx r12, r13, r8; x112, x111<- x99 * 0xffffffff
setc r10b; spill CF x52 to reg (r10)
clc;
adcx r13, [ rsp + 0x20 ]
adox r13, rcx
seto cl; spill OF x121 to reg (rcx)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rdx; loading flag
adox r11, rax
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, rax, rdi; x87, x86<- x2 * arg1[2]
mov rdx, 0xffffffff00000001 ; moving imm to reg
mov [ rsp + 0x48 ], r13; spilling x120 to mem
mulx rbp, r13, rbp; x65, x64<- x54 * 0xffffffff00000001
movzx rdx, r10b; x53, copying x52 here, cause x52 is needed in a reg for other than x53, namely all: , x53, size: 1
lea rdx, [ rdx + r14 ]
mov r14, 0x0 ; moving imm to reg
adcx r12, r14
movzx r10, byte [ rsp + 0x38 ]; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox r10, rdx
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx r11, r13
adcx rbp, r10
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, rbx, rdi; x85, x84<- x2 * arg1[3]
setc dl; spill CF x82 to reg (rdx)
movzx r13, byte [ rsp + 0x40 ]; load byte memx93 to register64
clc;
mov r10, -0x1 ; moving imm to reg
adcx r13, r10; loading flag
adcx rax, [ rsp + 0x30 ]
mov r13, [ rsi + 0x18 ]; load m64 x3 to register64
adcx rbx, r9
movzx r9, dl; x83, copying x82 here, cause x82 is needed in a reg for other than x83, namely all: , x83, size: 1
adox r9, r14
adc rdi, 0x0
add r15b, 0x7F; load flag from rm/8 into OF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
seto r15b; since that has deps, resore it whereever it was
adox r11, rax
mov r15, 0xffffffff00000001 ; moving imm to reg
mov rdx, r15; 0xffffffff00000001 to rdx
mulx r8, r15, r8; x110, x109<- x99 * 0xffffffff00000001
adox rbx, rbp
mov rbp, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rax, r14, r13; x130, x129<- x3 * arg1[3]
movzx rcx, cl
adcx rcx, r10; loading flag
adcx r11, r12
mov rdx, r13; x3 to rdx
mulx r13, rcx, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
adcx r15, rbx
adox rdi, r9
mulx r12, r9, [ rsi + 0x0 ]; x136, x135<- x3 * arg1[0]
adcx r8, rdi
seto bl; spill OF x108 to reg (rbx)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x48 ]
movzx rdi, bl; x128, copying x108 here, cause x108 is needed in a reg for other than x128, namely all: , x128, size: 1
adcx rdi, r10
clc;
adcx rcx, r12
mulx rdx, rbx, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
adcx rbx, r13
adox rcx, r11
adox rbx, r15
adcx r14, rdx
adox r14, r8
mov r11, 0xffffffff ; moving imm to reg
mov rdx, r9; x144 to rdx
mulx r9, r13, r11; x157, x156<- x144 * 0xffffffff
adcx rax, r10
mov r15, 0xffffffffffffffff ; moving imm to reg
mulx r12, r8, r15; x159, x158<- x144 * 0xffffffffffffffff
clc;
adcx r13, r12
adcx r9, r10
adox rax, rdi
clc;
adcx r8, rdx
mulx rdx, r8, rbp; x155, x154<- x144 * 0xffffffff00000001
adcx r13, rcx
adcx r9, rbx
adcx r8, r14
setc dil; spill CF x170 to reg (rdi)
seto cl; spill OF x153 to reg (rcx)
mov rbx, r13; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, x184, size: 2
sub rbx, r15
mov r14, r9; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
sbb r14, r11
mov r12, r8; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r12, 0x00000000
dec r10; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdi, dil
adox rdi, r10; loading flag
adox rax, rdx
movzx rdx, cl; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
mov rdi, 0x0 ; moving imm to reg
adox rdx, rdi
mov rcx, rax; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x180--x181, x187, size: 2
sbb rcx, rbp
sbb rdx, 0x00000000
cmovc r12, r8; if CF, x186<- x169 (nzVar)
cmovc r14, r9; if CF, x185<- x167 (nzVar)
cmovc rbx, r13; if CF, x184<- x165 (nzVar)
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x8 ], r14; out1[1] = x185
cmovc rcx, rax; if CF, x187<- x171 (nzVar)
mov [ rdx + 0x10 ], r12; out1[2] = x186
mov [ rdx + 0x18 ], rcx; out1[3] = x187
mov [ rdx + 0x0 ], rbx; out1[0] = x184
mov rbx, [ rsp + 0x50 ]; restoring from stack
mov rbp, [ rsp + 0x58 ]; restoring from stack
mov r12, [ rsp + 0x60 ]; restoring from stack
mov r13, [ rsp + 0x68 ]; restoring from stack
mov r14, [ rsp + 0x70 ]; restoring from stack
mov r15, [ rsp + 0x78 ]; restoring from stack
add rsp, 0x80 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 50.72, best 36.14159292035398, lastGood 37.256637168141594
; seed 4276274868767468 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1141701 ms / 60000 runs=> 19.02835ms/run
; Time spent for assembling and measureing (initial batch_size=219, initial num_batches=101): 456049 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.3994469655365109
; number reverted permutation/ tried permutation: 24263 / 30108 =80.587%
; number reverted decision/ tried decision: 23017 / 29893 =76.998%