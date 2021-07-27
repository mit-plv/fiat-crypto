SECTION .text
	GLOBAL mul_p256
mul_p256:
sub rsp, 0x70 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x40 ], rbx; saving to stack
mov [ rsp + 0x48 ], rbp; saving to stack
mov [ rsp + 0x50 ], r12; saving to stack
mov [ rsp + 0x58 ], r13; saving to stack
mov [ rsp + 0x60 ], r14; saving to stack
mov [ rsp + 0x68 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rdx + 0x8 ]; saving arg2[1] in rdx.
mulx r11, rbx, rax; x10, x9<- x4 * arg2[1]
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rbp, r12, rax; x12, x11<- x4 * arg2[0]
mov r13, 0xffffffffffffffff ; moving imm to reg
mov rdx, r13; 0xffffffffffffffff to rdx
mulx r13, r14, r12; x25, x24<- x11 * 0xffffffffffffffff
mov r15, 0xffffffff ; moving imm to reg
xchg rdx, r15; 0xffffffff, swapping with 0xffffffffffffffff, which is currently in rdx
mulx rcx, r8, r12; x23, x22<- x11 * 0xffffffff
xor r9, r9
adox r14, r12
adcx r8, r13
mov r14, [ rsi + 0x8 ]; load m64 x1 to register64
adcx rcx, r9
mov r13, rdx; preserving value of 0xffffffff into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r9, r15, r14; x44, x43<- x1 * arg2[1]
clc;
adcx rbx, rbp
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rbp, r13, r14; x46, x45<- x1 * arg2[0]
adox r8, rbx
seto bl; spill OF x32 to reg (rbx)
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r8
mov rdx, [ r10 + 0x10 ]; arg2[2] to rdx
mulx r8, rdi, rax; x8, x7<- x4 * arg2[2]
mov [ rsp + 0x8 ], r9; spilling x44 to mem
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r9; 0xffffffffffffffff to rdx
mov [ rsp + 0x10 ], r12; spilling x11 to mem
mulx r9, r12, r13; x69, x68<- x54 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x18 ], r8; spilling x8 to mem
mov [ rsp + 0x20 ], r9; spilling x69 to mem
mulx r8, r9, r13; x67, x66<- x54 * 0xffffffff
adcx rdi, r11
setc r11b; spill CF x16 to reg (r11)
clc;
adcx r15, rbp
setc bpl; spill CF x48 to reg (rbp)
clc;
mov rdx, -0x1 ; moving imm to reg
movzx rbx, bl
adcx rbx, rdx; loading flag
adcx rdi, rcx
setc cl; spill CF x34 to reg (rcx)
clc;
adcx r12, r13
adox r15, rdi
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx rax, r12, rax; x6, x5<- x4 * arg2[3]
seto bl; spill OF x57 to reg (rbx)
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, [ rsp + 0x20 ]
mov rdi, 0x0 ; moving imm to reg
adox r8, rdi
dec rdi; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r11, r11b
adox r11, rdi; loading flag
adox r12, [ rsp + 0x18 ]
mov r11, 0xffffffff00000001 ; moving imm to reg
mov rdx, r11; 0xffffffff00000001 to rdx
mulx r11, rdi, [ rsp + 0x10 ]; x21, x20<- x11 * 0xffffffff00000001
mov rdx, 0x0 ; moving imm to reg
adox rax, rdx
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rcx, cl
adox rcx, rdx; loading flag
adox r12, rdi
mov rdx, r14; x1 to rdx
mulx r14, rcx, [ r10 + 0x10 ]; x42, x41<- x1 * arg2[2]
adcx r9, r15
mov r15, [ rsi + 0x10 ]; load m64 x2 to register64
adox r11, rax
seto dil; spill OF x38 to reg (rdi)
mov rax, 0x0 ; moving imm to reg
dec rax; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rax; loading flag
adox rcx, [ rsp + 0x8 ]
mulx rdx, rbp, [ r10 + 0x18 ]; x40, x39<- x1 * arg2[3]
adox rbp, r14
mov r14, 0x0 ; moving imm to reg
adox rdx, r14
dec r14; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx rbx, bl
adox rbx, r14; loading flag
adox r12, rcx
adcx r8, r12
adox rbp, r11
movzx rax, dil; x62, copying x38 here, cause x38 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox rax, rdx
mov rbx, 0xffffffff00000001 ; moving imm to reg
mov rdx, rbx; 0xffffffff00000001 to rdx
mulx r13, rbx, r13; x65, x64<- x54 * 0xffffffff00000001
adcx rbx, rbp
adcx r13, rax
seto dil; spill OF x83 to reg (rdi)
adc dil, 0x0
movzx rdi, dil
mov r11, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rcx, r12, r15; x91, x90<- x2 * arg2[0]
adox r12, r9
mov r9, 0xffffffffffffffff ; moving imm to reg
mov rdx, r12; x99 to rdx
mulx r12, rbp, r9; x114, x113<- x99 * 0xffffffffffffffff
adcx rbp, rdx
mov rbp, 0xffffffff ; moving imm to reg
mulx rax, r14, rbp; x112, x111<- x99 * 0xffffffff
mov rbp, rdx; preserving value of x99 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mulx r9, r11, r15; x89, x88<- x2 * arg2[1]
mov byte [ rsp + 0x28 ], dil; spilling byte x83 to mem
setc dil; spill CF x119 to reg (rdi)
clc;
adcx r11, rcx
adox r11, r8
seto r8b; spill OF x102 to reg (r8)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r12
mov rdx, r15; x2 to rdx
mulx r15, r12, [ r10 + 0x18 ]; x85, x84<- x2 * arg2[3]
mov rcx, 0x0 ; moving imm to reg
adox rax, rcx
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdi, dil
adox rdi, rcx; loading flag
adox r11, r14
mulx rdx, rdi, [ r10 + 0x10 ]; x87, x86<- x2 * arg2[2]
adcx rdi, r9
mov r9, [ rsi + 0x18 ]; load m64 x3 to register64
adcx r12, rdx
mov r14, 0x0 ; moving imm to reg
adcx r15, r14
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx rbp, r14, rbp; x110, x109<- x99 * 0xffffffff00000001
clc;
movzx r8, r8b
adcx r8, rcx; loading flag
adcx rbx, rdi
adox rax, rbx
adcx r12, r13
movzx r13, byte [ rsp + 0x28 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx r13, r15
mov r8, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ r10 + 0x0 ]; saving arg2[0] in rdx.
mulx rdi, r15, r9; x136, x135<- x3 * arg2[0]
adox r14, r12
adox rbp, r13
seto bl; spill OF x128 to reg (rbx)
adc bl, 0x0
movzx rbx, bl
adox r15, r11
mov r11, 0xffffffffffffffff ; moving imm to reg
mov rdx, r15; x144 to rdx
mulx r15, r12, r11; x159, x158<- x144 * 0xffffffffffffffff
mov r13, 0xffffffff ; moving imm to reg
mulx rcx, r11, r13; x157, x156<- x144 * 0xffffffff
mov r13, rdx; preserving value of x144 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov byte [ rsp + 0x30 ], bl; spilling byte x128 to mem
mulx r8, rbx, r9; x134, x133<- x3 * arg2[1]
adcx rbx, rdi
adox rbx, rax
setc al; spill CF x138 to reg (rax)
clc;
adcx r11, r15
mov rdi, 0x0 ; moving imm to reg
adcx rcx, rdi
clc;
adcx r12, r13
adcx r11, rbx
setc r12b; spill CF x166 to reg (r12)
seto r15b; spill OF x147 to reg (r15)
mov rbx, r11; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, x184, size: 2
mov [ rsp + 0x38 ], rcx; spilling x162 to mem
mov rcx, 0xffffffffffffffff ; moving imm to reg
sub rbx, rcx
mov rdx, r9; x3 to rdx
mulx r9, rdi, [ r10 + 0x10 ]; x132, x131<- x3 * arg2[2]
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx rax, al
adox rax, rcx; loading flag
adox r8, rdi
mulx rdx, rax, [ r10 + 0x18 ]; x130, x129<- x3 * arg2[3]
adox rax, r9
mov r9, 0x0 ; moving imm to reg
adox rdx, r9
dec r9; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r15, r15b
adox r15, r9; loading flag
adox r14, r8
adox rax, rbp
movzx rcx, byte [ rsp + 0x30 ]; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adox rcx, rdx
seto bpl; spill OF x153 to reg (rbp)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r15; loading flag
adox r14, [ rsp + 0x38 ]
mov r12, 0xffffffff00000001 ; moving imm to reg
mov rdx, r13; x144 to rdx
mulx rdx, r13, r12; x155, x154<- x144 * 0xffffffff00000001
adox r13, rax
seto dil; spill OF x170 to reg (rdi)
mov r8, r14; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
mov rax, 0xffffffff ; moving imm to reg
sbb r8, rax
mov r15, r13; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x186, x178--x179, size: 2
sbb r15, 0x00000000
dec r9; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdi, dil
adox rdi, r9; loading flag
adox rcx, rdx
movzx rdx, bpl; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
mov rdi, 0x0 ; moving imm to reg
adox rdx, rdi
mov rbp, rcx; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x187, x180--x181, size: 2
sbb rbp, r12
sbb rdx, 0x00000000
cmovc r8, r14; if CF, x185<- x167 (nzVar)
cmovc rbx, r11; if CF, x184<- x165 (nzVar)
cmovc r15, r13; if CF, x186<- x169 (nzVar)
mov r11, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r11 + 0x0 ], rbx; out1[0] = x184
cmovc rbp, rcx; if CF, x187<- x171 (nzVar)
mov [ r11 + 0x10 ], r15; out1[2] = x186
mov [ r11 + 0x8 ], r8; out1[1] = x185
mov [ r11 + 0x18 ], rbp; out1[3] = x187
mov rbx, [ rsp + 0x40 ]; restoring from stack
mov rbp, [ rsp + 0x48 ]; restoring from stack
mov r12, [ rsp + 0x50 ]; restoring from stack
mov r13, [ rsp + 0x58 ]; restoring from stack
mov r14, [ rsp + 0x60 ]; restoring from stack
mov r15, [ rsp + 0x68 ]; restoring from stack
add rsp, 0x70 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 50.17, best 33.56277056277056, lastGood 34.45887445887446
; seed 2381330932113131 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1076124 ms / 60000 runs=> 17.9354ms/run
; Time spent for assembling and measureing (initial batch_size=227, initial num_batches=101): 401505 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.37310291379060406
; number reverted permutation/ tried permutation: 24681 / 29826 =82.750%
; number reverted decision/ tried decision: 23414 / 30175 =77.594%