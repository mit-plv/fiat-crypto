SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0x60 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x30 ], rbx; saving to stack
mov [ rsp + 0x38 ], rbp; saving to stack
mov [ rsp + 0x40 ], r12; saving to stack
mov [ rsp + 0x48 ], r13; saving to stack
mov [ rsp + 0x50 ], r14; saving to stack
mov [ rsp + 0x58 ], r15; saving to stack
mov rax, [ rsi + 0x8 ]; load m64 x1 to register64
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r10, r11, rax; x44, x43<- x1 * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rbp, rax; x40, x39<- x1 * arg1[3]
mov rdx, rax; x1 to rdx
mulx rax, r12, [ rsi + 0x0 ]; x46, x45<- x1 * arg1[0]
mov r13, [ rsi + 0x0 ]; load m64 x4 to register64
xor r14, r14
adox r11, rax
mulx rdx, r15, [ rsi + 0x10 ]; x42, x41<- x1 * arg1[2]
adox r15, r10
adox rbp, rdx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r8, r13; x12, x11<- x4 * arg1[0]
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r9, r10, r8; x25, x24<- x11 * 0xffffffffffffffff
adox rbx, r14
mov rax, 0xffffffff ; moving imm to reg
xchg rdx, r8; x11, swapping with 0xffffffffffffffff, which is currently in rdx
mulx r14, r8, rax; x23, x22<- x11 * 0xffffffff
adcx r10, rdx
mov r10, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rax, rdi, r13; x10, x9<- x4 * arg1[1]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r9
seto r9b; spill OF x27 to reg (r9)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, rcx
adcx r8, rdi
setc cl; spill CF x32 to reg (rcx)
clc;
adcx r12, r8
xchg rdx, r13; x4, swapping with 0x0, which is currently in rdx
mulx rdi, r8, [ rsi + 0x10 ]; x8, x7<- x4 * arg1[2]
mov r13, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r12; x54, swapping with x4, which is currently in rdx
mov [ rsp + 0x8 ], rbx; spilling x53 to mem
mov [ rsp + 0x10 ], rbp; spilling x51 to mem
mulx rbx, rbp, r13; x69, x68<- x54 * 0xffffffffffffffff
adox r8, rax
xchg rdx, r12; x4, swapping with x54, which is currently in rdx
mulx rdx, rax, [ rsi + 0x18 ]; x6, x5<- x4 * arg1[3]
movzx r13, r9b; x28, copying x27 here, cause x27 is needed in a reg for other than x28, namely all: , x28, size: 1
lea r13, [ r13 + r14 ]
setc r14b; spill CF x55 to reg (r14)
clc;
adcx rbp, r12
mov rbp, 0xffffffff ; moving imm to reg
xchg rdx, rbp; 0xffffffff, swapping with x6, which is currently in rdx
mov [ rsp + 0x18 ], r15; spilling x49 to mem
mulx r9, r15, r12; x67, x66<- x54 * 0xffffffff
adox rax, rdi
setc dil; spill CF x74 to reg (rdi)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdx; loading flag
adcx r8, r13
mov rcx, 0x0 ; moving imm to reg
adox rbp, rcx
mov r13, 0xffffffff00000001 ; moving imm to reg
mov rdx, r13; 0xffffffff00000001 to rdx
mulx r10, r13, r10; x21, x20<- x11 * 0xffffffff00000001
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, rbx
adcx r13, rax
seto bl; spill OF x71 to reg (rbx)
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r14, r14b
adox r14, rcx; loading flag
adox r8, r11
mov r11, [ rsp + 0x18 ]; x58, copying x49 here, cause x49 is needed in a reg for other than x58, namely all: , x58--x59, size: 1
adox r11, r13
adcx r10, rbp
mov r14, [ rsp + 0x10 ]; x60, copying x51 here, cause x51 is needed in a reg for other than x60, namely all: , x60--x61, size: 1
adox r14, r10
setc al; spill CF x38 to reg (rax)
clc;
movzx rdi, dil
adcx rdi, rcx; loading flag
adcx r8, r15
movzx rdi, bl; x72, copying x71 here, cause x71 is needed in a reg for other than x72, namely all: , x72, size: 1
lea rdi, [ rdi + r9 ]
mov r9, 0xffffffff00000001 ; moving imm to reg
mov rdx, r9; 0xffffffff00000001 to rdx
mulx r12, r9, r12; x65, x64<- x54 * 0xffffffff00000001
mov rbp, [ rsi + 0x10 ]; load m64 x2 to register64
adcx rdi, r11
movzx rax, al
mov r15, [ rsp + 0x8 ]; x62, copying x53 here, cause x53 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox r15, rax
mov rbx, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, r11, rbp; x91, x90<- x2 * arg1[0]
mov rdx, rbp; x2 to rdx
mulx rbp, rax, [ rsi + 0x8 ]; x89, x88<- x2 * arg1[1]
adcx r9, r14
adcx r12, r15
seto r10b; spill OF x83 to reg (r10)
adc r10b, 0x0
movzx r10, r10b
adox rax, r13
mulx r14, r15, [ rsi + 0x10 ]; x87, x86<- x2 * arg1[2]
adox r15, rbp
mulx rdx, r13, [ rsi + 0x18 ]; x85, x84<- x2 * arg1[3]
adox r13, r14
adcx r11, r8
adcx rax, rdi
adcx r15, r9
mov r8, 0xffffffff ; moving imm to reg
xchg rdx, r8; 0xffffffff, swapping with x85, which is currently in rdx
mulx rdi, rbp, r11; x112, x111<- x99 * 0xffffffff
mov r9, 0x0 ; moving imm to reg
adox r8, r9
adcx r13, r12
mov r12, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r11; x99, swapping with 0xffffffff, which is currently in rdx
mulx r14, r9, r12; x114, x113<- x99 * 0xffffffffffffffff
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r14
adox rdi, rcx
movzx r14, r10b; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx r14, r8
mulx r10, r8, rbx; x110, x109<- x99 * 0xffffffff00000001
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, rdx
adox rbp, rax
mov r9, [ rsi + 0x18 ]; load m64 x3 to register64
adox rdi, r15
adox r8, r13
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, r15, r9; x136, x135<- x3 * arg1[0]
mov rdx, r9; x3 to rdx
mulx r9, r13, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
adox r10, r14
seto r14b; spill OF x127 to reg (r14)
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, rbp
movzx rbp, r14b; x128, copying x127 here, cause x127 is needed in a reg for other than x128, namely all: , x128, size: 1
adcx rbp, rcx
mov r14, 0xffffffffffffffff ; moving imm to reg
xchg rdx, r15; x144, swapping with x3, which is currently in rdx
mulx rcx, r12, r14; x159, x158<- x144 * 0xffffffffffffffff
mulx r14, rbx, r11; x157, x156<- x144 * 0xffffffff
clc;
adcx rbx, rcx
xchg rdx, r15; x3, swapping with x144, which is currently in rdx
mulx rcx, r11, [ rsi + 0x18 ]; x130, x129<- x3 * arg1[3]
mov [ rsp + 0x20 ], rbp; spilling x128 to mem
mulx rdx, rbp, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
mov [ rsp + 0x28 ], r10; spilling x126 to mem
setc r10b; spill CF x161 to reg (r10)
clc;
adcx r13, rax
adox r13, rdi
movzx rdi, r10b; x162, copying x161 here, cause x161 is needed in a reg for other than x162, namely all: , x162, size: 1
lea rdi, [ rdi + r14 ]
setc al; spill CF x138 to reg (rax)
clc;
adcx r12, r15
adcx rbx, r13
setc r12b; spill CF x166 to reg (r12)
seto r14b; spill OF x147 to reg (r14)
mov r10, rbx; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, x184, size: 2
mov r13, 0xffffffffffffffff ; moving imm to reg
sub r10, r13
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, r13; loading flag
adox r9, rbp
adox r11, rdx
mov rdx, 0x0 ; moving imm to reg
adox rcx, rdx
inc r13; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdx; loading flag
adox r8, r9
mov rbp, [ rsp + 0x28 ]; x150, copying x126 here, cause x126 is needed in a reg for other than x150, namely all: , x150--x151, size: 1
adox rbp, r11
mov rax, [ rsp + 0x20 ]; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox rax, rcx
mov r14, 0xffffffff00000001 ; moving imm to reg
mov rdx, r14; 0xffffffff00000001 to rdx
mulx r15, r14, r15; x155, x154<- x144 * 0xffffffff00000001
seto r9b; spill OF x153 to reg (r9)
dec r13; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r12, r12b
adox r12, r13; loading flag
adox r8, rdi
adox r14, rbp
seto dil; spill OF x170 to reg (rdi)
mov r12, r8; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x176--x177, x185, size: 2
mov r11, 0xffffffff ; moving imm to reg
sbb r12, r11
mov rcx, r14; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb rcx, 0x00000000
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rbp; loading flag
adox rax, r15
movzx r15, r9b; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
adox r15, r13
mov r9, rax; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
sbb r9, rdx
sbb r15, 0x00000000
cmovc r9, rax; if CF, x187<- x171 (nzVar)
cmovc rcx, r14; if CF, x186<- x169 (nzVar)
cmovc r12, r8; if CF, x185<- x167 (nzVar)
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x8 ], r12; out1[1] = x185
mov [ r15 + 0x10 ], rcx; out1[2] = x186
mov [ r15 + 0x18 ], r9; out1[3] = x187
cmovc r10, rbx; if CF, x184<- x165 (nzVar)
mov [ r15 + 0x0 ], r10; out1[0] = x184
mov rbx, [ rsp + 0x30 ]; restoring from stack
mov rbp, [ rsp + 0x38 ]; restoring from stack
mov r12, [ rsp + 0x40 ]; restoring from stack
mov r13, [ rsp + 0x48 ]; restoring from stack
mov r14, [ rsp + 0x50 ]; restoring from stack
mov r15, [ rsp + 0x58 ]; restoring from stack
add rsp, 0x60 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 99.56, best 78.47826086956522, lastGood 83.0989010989011
; seed 4285393296769624 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 844304 ms / 60000 runs=> 14.071733333333333ms/run
; Time spent for assembling and measureing (initial batch_size=91, initial num_batches=101): 207586 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.24586641778316815
; number reverted permutation/ tried permutation: 25320 / 30063 =84.223%
; number reverted decision/ tried decision: 22299 / 29938 =74.484%