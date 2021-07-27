SECTION .text
	GLOBAL square_p256
square_p256:
sub rsp, 0x68 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x38 ], rbx; saving to stack
mov [ rsp + 0x40 ], rbp; saving to stack
mov [ rsp + 0x48 ], r12; saving to stack
mov [ rsp + 0x50 ], r13; saving to stack
mov [ rsp + 0x58 ], r14; saving to stack
mov [ rsp + 0x60 ], r15; saving to stack
mov rax, [ rsi + 0x0 ]; load m64 x4 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, rax; x12, x11<- x4 * arg1[0]
mov rbx, 0xffffffffffffffff ; moving imm to reg
mov rdx, r11; x11 to rdx
mulx r11, rbp, rbx; x25, x24<- x11 * 0xffffffffffffffff
test al, al
adox rbp, rdx
mov rbp, 0xffffffff ; moving imm to reg
mulx r12, r13, rbp; x23, x22<- x11 * 0xffffffff
mov r14, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, rcx, rax; x10, x9<- x4 * arg1[1]
adcx rcx, r10
mov rdx, [ rsi + 0x8 ]; load m64 x1 to register64
mulx r8, r9, [ rsi + 0x0 ]; x46, x45<- x1 * arg1[0]
setc r10b; spill CF x14 to reg (r10)
clc;
adcx r13, r11
adox r13, rcx
setc r11b; spill CF x27 to reg (r11)
clc;
adcx r9, r13
xchg rdx, rbx; 0xffffffffffffffff, swapping with x1, which is currently in rdx
mulx rcx, r13, r9; x69, x68<- x54 * 0xffffffffffffffff
mov rbp, rdx; preserving value of 0xffffffffffffffff into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r14; spilling x11 to mem
mulx rdi, r14, rax; x8, x7<- x4 * arg1[2]
setc dl; spill CF x55 to reg (rdx)
clc;
adcx r13, r9
setc r13b; spill CF x74 to reg (r13)
clc;
mov rbp, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rbp; loading flag
adcx r15, r14
movzx r10, r11b; x28, copying x27 here, cause x27 is needed in a reg for other than x28, namely all: , x28, size: 1
lea r10, [ r10 + r12 ]
mov r12b, dl; preserving value of x55 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, r14, rbx; x44, x43<- x1 * arg1[1]
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], r11; spilling x44 to mem
mulx rbp, r11, r9; x67, x66<- x54 * 0xffffffff
adox r10, r15
seto r15b; spill OF x34 to reg (r15)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r8
seto r8b; spill OF x48 to reg (r8)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rdx; loading flag
adox r10, r14
seto r12b; spill OF x57 to reg (r12)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rcx
seto cl; spill OF x71 to reg (rcx)
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r13, r13b
adox r13, rdx; loading flag
adox r10, r11
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rax, r13, rax; x6, x5<- x4 * arg1[3]
adcx r13, rdi
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx rdi, r14, [ rsp + 0x8 ]; x21, x20<- x11 * 0xffffffff00000001
seto r11b; spill OF x76 to reg (r11)
mov rdx, 0x0 ; moving imm to reg
dec rdx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rdx; loading flag
adox r13, r14
mov r15, 0x0 ; moving imm to reg
adcx rax, r15
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r15, rbx; x42, x41<- x1 * arg1[2]
movzx rdx, cl; x72, copying x71 here, cause x71 is needed in a reg for other than x72, namely all: , x72, size: 1
lea rdx, [ rdx + rbp ]
adox rdi, rax
mov rbp, rdx; preserving value of x72 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, rcx, rbx; x40, x39<- x1 * arg1[3]
clc;
mov rdx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rdx; loading flag
adcx r15, [ rsp + 0x10 ]
adcx rcx, r14
mov r8, 0x0 ; moving imm to reg
adcx rbx, r8
clc;
movzx r12, r12b
adcx r12, rdx; loading flag
adcx r13, r15
mov r12, 0xffffffff00000001 ; moving imm to reg
mov rdx, r12; 0xffffffff00000001 to rdx
mulx r9, r12, r9; x65, x64<- x54 * 0xffffffff00000001
adcx rcx, rdi
setc al; spill CF x61 to reg (rax)
clc;
mov r14, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r14; loading flag
adcx r13, rbp
movzx r11, al; x62, copying x61 here, cause x61 is needed in a reg for other than x62, namely all: , x62--x63, size: 1
adox r11, rbx
adcx r12, rcx
mov rbp, [ rsi + 0x10 ]; load m64 x2 to register64
adcx r9, r11
seto dil; spill OF x83 to reg (rdi)
adc dil, 0x0
movzx rdi, dil
mov r15, rdx; preserving value of 0xffffffff00000001 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, rax, rbp; x91, x90<- x2 * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r11, rbp; x89, x88<- x2 * arg1[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r14, rbp; x87, x86<- x2 * arg1[2]
adox r11, rbx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, rbx, rbp; x85, x84<- x2 * arg1[3]
adcx rax, r10
adox r14, rcx
mov rdx, 0xffffffffffffffff ; moving imm to reg
mulx r10, rcx, rax; x114, x113<- x99 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov byte [ rsp + 0x18 ], dil; spilling byte x83 to mem
mulx r15, rdi, rax; x112, x111<- x99 * 0xffffffff
adox rbx, r8
mov r8, 0x0 ; moving imm to reg
adox rbp, r8
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rcx, rax
mov rcx, [ rsi + 0x18 ]; load m64 x3 to register64
setc dl; spill CF x100 to reg (rdx)
clc;
adcx rdi, r10
setc r10b; spill CF x116 to reg (r10)
clc;
mov r8, -0x1 ; moving imm to reg
movzx rdx, dl
adcx rdx, r8; loading flag
adcx r13, r11
adox rdi, r13
mov rdx, rcx; x3 to rdx
mulx rcx, r11, [ rsi + 0x0 ]; x136, x135<- x3 * arg1[0]
seto r13b; spill OF x121 to reg (r13)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, rdi
mov rdi, 0xffffffffffffffff ; moving imm to reg
xchg rdx, rdi; 0xffffffffffffffff, swapping with x3, which is currently in rdx
mov [ rsp + 0x20 ], rcx; spilling x136 to mem
mulx r8, rcx, r11; x159, x158<- x144 * 0xffffffffffffffff
mov rdx, 0xffffffff ; moving imm to reg
mov [ rsp + 0x28 ], rcx; spilling x158 to mem
mov byte [ rsp + 0x30 ], r13b; spilling byte x121 to mem
mulx rcx, r13, r11; x157, x156<- x144 * 0xffffffff
adcx r14, r12
seto r12b; spill OF x145 to reg (r12)
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r8
movzx r8, r10b; x117, copying x116 here, cause x116 is needed in a reg for other than x117, namely all: , x117, size: 1
lea r8, [ r8 + r15 ]
mov r15, 0x0 ; moving imm to reg
adox rcx, r15
adcx rbx, r9
movzx r9, byte [ rsp + 0x18 ]; x107, copying x83 here, cause x83 is needed in a reg for other than x107, namely all: , x107--x108, size: 1
adcx r9, rbp
movzx rbp, byte [ rsp + 0x30 ]; load byte memx121 to register64
dec r15; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
adox rbp, r15; loading flag
adox r14, r8
mov rdx, 0xffffffff00000001 ; moving imm to reg
mulx rax, r10, rax; x110, x109<- x99 * 0xffffffff00000001
adox r10, rbx
adox rax, r9
xchg rdx, rdi; x3, swapping with 0xffffffff00000001, which is currently in rdx
mulx rbp, r8, [ rsi + 0x8 ]; x134, x133<- x3 * arg1[1]
seto bl; spill OF x128 to reg (rbx)
adc bl, 0x0
movzx rbx, bl
adox r8, [ rsp + 0x20 ]
mulx r9, r15, [ rsi + 0x10 ]; x132, x131<- x3 * arg1[2]
adox r15, rbp
mulx rdx, rbp, [ rsi + 0x18 ]; x130, x129<- x3 * arg1[3]
adox rbp, r9
mov r9, 0x0 ; moving imm to reg
adox rdx, r9
add r12b, 0xFF; load flag from rm/8 into CF, clears other flag. NODE, if operand1 is not a byte reg, this fails.
setc r12b; since that has deps, resore it whereever it was
adcx r14, r8
mov r12, r11; _, copying x144 here, cause x144 is needed in a reg for other than _, namely all: , x154--x155, _--x164, size: 2
adox r12, [ rsp + 0x28 ]
adcx r15, r10
adox r13, r14
adcx rbp, rax
movzx r12, bl; x152, copying x128 here, cause x128 is needed in a reg for other than x152, namely all: , x152--x153, size: 1
adcx r12, rdx
adox rcx, r15
mov rdx, rdi; 0xffffffff00000001 to rdx
mulx r11, r10, r11; x155, x154<- x144 * 0xffffffff00000001
setc al; spill CF x153 to reg (rax)
seto bl; spill OF x168 to reg (rbx)
mov r8, r13; x174, copying x165 here, cause x165 is needed in a reg for other than x174, namely all: , x174--x175, x184, size: 2
mov r14, 0xffffffffffffffff ; moving imm to reg
sub r8, r14
mov r15, rcx; x176, copying x167 here, cause x167 is needed in a reg for other than x176, namely all: , x185, x176--x177, size: 2
mov r9, 0xffffffff ; moving imm to reg
sbb r15, r9
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, r9; loading flag
adox rbp, r10
adox r11, r12
movzx r12, al; x173, copying x153 here, cause x153 is needed in a reg for other than x173, namely all: , x173, size: 1
mov rbx, 0x0 ; moving imm to reg
adox r12, rbx
mov rax, rbp; x178, copying x169 here, cause x169 is needed in a reg for other than x178, namely all: , x178--x179, x186, size: 2
sbb rax, 0x00000000
mov r10, r11; x180, copying x171 here, cause x171 is needed in a reg for other than x180, namely all: , x180--x181, x187, size: 2
sbb r10, rdx
sbb r12, 0x00000000
cmovc r10, r11; if CF, x187<- x171 (nzVar)
cmovc rax, rbp; if CF, x186<- x169 (nzVar)
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x10 ], rax; out1[2] = x186
cmovc r8, r13; if CF, x184<- x165 (nzVar)
cmovc r15, rcx; if CF, x185<- x167 (nzVar)
mov [ r12 + 0x0 ], r8; out1[0] = x184
mov [ r12 + 0x8 ], r15; out1[1] = x185
mov [ r12 + 0x18 ], r10; out1[3] = x187
mov rbx, [ rsp + 0x38 ]; restoring from stack
mov rbp, [ rsp + 0x40 ]; restoring from stack
mov r12, [ rsp + 0x48 ]; restoring from stack
mov r13, [ rsp + 0x50 ]; restoring from stack
mov r14, [ rsp + 0x58 ]; restoring from stack
mov r15, [ rsp + 0x60 ]; restoring from stack
add rsp, 0x68 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 64.375, best 53.17763157894737, lastGood 54.71052631578947
; seed 815469023996179 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 584414 ms / 60000 runs=> 9.740233333333334ms/run
; Time spent for assembling and measureing (initial batch_size=152, initial num_batches=101): 177925 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.3044502698429538
; number reverted permutation/ tried permutation: 26401 / 29886 =88.339%
; number reverted decision/ tried decision: 23694 / 30115 =78.678%