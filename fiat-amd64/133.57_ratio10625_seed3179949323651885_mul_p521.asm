SECTION .text
	GLOBAL mul_p521
mul_p521:
sub rsp, 0x2b8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x288 ], rbx; saving to stack
mov [ rsp + 0x290 ], rbp; saving to stack
mov [ rsp + 0x298 ], r12; saving to stack
mov [ rsp + 0x2a0 ], r13; saving to stack
mov [ rsp + 0x2a8 ], r14; saving to stack
mov [ rsp + 0x2b0 ], r15; saving to stack
imul rax, [ rdx + 0x38 ], 0x2; x10001 <- arg2[7] * 0x2
imul r10, [ rdx + 0x40 ], 0x2; x10000 <- arg2[8] * 0x2
imul r11, [ rdx + 0x28 ], 0x2; x10003 <- arg2[5] * 0x2
mov rbx, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rbp, r12, rax; x70, x69<- arg1[2] * x10001
mov rdx, r10; x10000 to rdx
mulx r10, r13, [ rsi + 0x8 ]; x72, x71<- arg1[1] * x10000
imul r14, [ rbx + 0x8 ], 0x2; x10007 <- arg2[1] * 0x2
mov r15, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r8, [ rbx + 0x0 ]; x162, x161<- arg1[0] * arg2[0]
imul r9, [ rbx + 0x30 ], 0x2; x10002 <- arg2[6] * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
imul rdi, [ rbx + 0x20 ], 0x2; x10004 <- arg2[4] * 0x2
mov rdx, r9; x10002 to rdx
mov [ rsp + 0x8 ], rcx; spilling x162 to mem
mulx r9, rcx, [ rsi + 0x18 ]; x66, x65<- arg1[3] * x10002
mov [ rsp + 0x10 ], r10; spilling x72 to mem
mov r10, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x18 ], rbp; spilling x70 to mem
mov [ rsp + 0x20 ], r8; spilling x161 to mem
mulx rbp, r8, rdi; x52, x51<- arg1[5] * x10004
mov rdx, r14; x10007 to rdx
mulx rdx, r14, [ rsi + 0x40 ]; x16, x15<- arg1[8] * x10007
mov [ rsp + 0x28 ], rax; spilling x10001 to mem
mov rax, rdx; preserving value of x16 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x30 ], r13; spilling x71 to mem
mov [ rsp + 0x38 ], r9; spilling x66 to mem
mulx r13, r9, r11; x60, x59<- arg1[4] * x10003
mov [ rsp + 0x40 ], r12; spilling x69 to mem
imul r12, [ rbx + 0x10 ], 0x2; x10006 <- arg2[2] * 0x2
mov [ rsp + 0x48 ], r13; spilling x60 to mem
imul r13, [ rbx + 0x18 ], 0x2; x10005 <- arg2[3] * 0x2
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x50 ], r15; spilling x10000 to mem
mov [ rsp + 0x58 ], rcx; spilling x65 to mem
mulx r15, rcx, r13; x42, x41<- arg1[6] * x10005
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x60 ], r9; spilling x59 to mem
mov [ rsp + 0x68 ], rbp; spilling x52 to mem
mulx r9, rbp, r12; x30, x29<- arg1[7] * x10006
add r14, rbp; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rcx
adcx r9, rax
clc;
adcx r14, r8
adox r15, r9
adcx r15, [ rsp + 0x68 ]
add r14, [ rsp + 0x60 ]; could be done better, if r0 has been u8 as well
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x48 ]
clc;
adcx r14, [ rsp + 0x40 ]
adox r15, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, rax, [ rbx + 0x0 ]; x144, x143<- arg1[1] * arg2[0]
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, [ rsp + 0x30 ]
setc r9b; spill CF x184 to reg (r9)
clc;
adcx r14, [ rsp + 0x20 ]
mov rdx, r10; x10002 to rdx
mulx r10, rbp, [ rsi + 0x20 ]; x58, x57<- arg1[4] * x10002
movzx r9, r9b
lea r15, [ r9 + r15 ]
mov r9, [ rsp + 0x18 ]
lea r15, [r9+r15]
adox r15, [ rsp + 0x10 ]
xchg rdx, r11; x10003, swapping with x10002, which is currently in rdx
mulx r9, rcx, [ rsi + 0x28 ]; x50, x49<- arg1[5] * x10003
xchg rdx, r12; x10006, swapping with x10003, which is currently in rdx
mov [ rsp + 0x70 ], r8; spilling x144 to mem
mulx rdx, r8, [ rsi + 0x40 ]; x14, x13<- arg1[8] * x10006
xchg rdx, r13; x10005, swapping with x14, which is currently in rdx
mov [ rsp + 0x78 ], rax; spilling x143 to mem
mov [ rsp + 0x80 ], r10; spilling x58 to mem
mulx rax, r10, [ rsi + 0x38 ]; x28, x27<- arg1[7] * x10005
mov [ rsp + 0x88 ], r9; spilling x50 to mem
mov r9, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x90 ], rbp; spilling x57 to mem
mov [ rsp + 0x98 ], rcx; spilling x49 to mem
mulx rbp, rcx, [ rsp + 0x28 ]; x64, x63<- arg1[3] * x10001
adcx r15, [ rsp + 0x8 ]
mov [ rsp + 0xa0 ], rbp; spilling x64 to mem
mov rbp, r14; x195, copying x191 here, cause x191 is needed in a reg for other than x195, namely all: , x197, x195, size: 2
shrd rbp, r15, 58; x195 <- x193||x191 >> 58
add r8, r10; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xa8 ], rbp; spilling x195 to mem
mulx r10, rbp, [ rsp + 0x50 ]; x68, x67<- arg1[2] * x10000
adcx rax, r13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xb0 ], r10; spilling x68 to mem
mulx r13, r10, rdi; x40, x39<- arg1[6] * x10004
mov [ rsp + 0xb8 ], rbp; spilling x67 to mem
xor rbp, rbp
adox r8, r10
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, rbp, [ rbx + 0x8 ]; x160, x159<- arg1[0] * arg2[1]
adcx r8, [ rsp + 0x98 ]
adox r13, rax
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, [ rsp + 0x90 ]
adcx r13, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xc0 ], r10; spilling x160 to mem
mulx rax, r10, rdi; x26, x25<- arg1[7] * x10004
clc;
adcx r8, rcx
adox r13, [ rsp + 0x80 ]
adcx r13, [ rsp + 0xa0 ]
xor rcx, rcx
adox r8, [ rsp + 0xb8 ]
adox r13, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r9, rcx, r9; x12, x11<- arg1[8] * x10005
adcx r8, [ rsp + 0x78 ]
mov [ rsp + 0xc8 ], r9; spilling x12 to mem
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, rbp
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbp, r9, [ rsp + 0x50 ]; x62, x61<- arg1[3] * x10000
adcx r13, [ rsp + 0x70 ]
adox r13, [ rsp + 0xc0 ]
mov rdx, [ rbx + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0xd0 ], rbp; spilling x62 to mem
mov [ rsp + 0xd8 ], r9; spilling x61 to mem
mulx rbp, r9, [ rsi + 0x8 ]; x142, x141<- arg1[1] * arg2[1]
shr r15, 58; x196 <- x193>> 58
test al, al
adox r8, [ rsp + 0xa8 ]
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0xe0 ], rbp; spilling x142 to mem
mov [ rsp + 0xe8 ], r9; spilling x141 to mem
mulx rbp, r9, [ rsi + 0x0 ]; x158, x157<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xf0 ], rbp; spilling x158 to mem
mov [ rsp + 0xf8 ], r9; spilling x157 to mem
mulx rbp, r9, r12; x38, x37<- arg1[6] * x10003
adox r15, r13
mov r13, r8; x458, copying x454 here, cause x454 is needed in a reg for other than x458, namely all: , x458, x460, size: 2
shrd r13, r15, 58; x458 <- x456||x454 >> 58
test al, al
adox rcx, r10
adox rax, [ rsp + 0xc8 ]
shr r15, 58; x459 <- x456>> 58
add rcx, r9; could be done better, if r0 has been u8 as well
mov rdx, r11; x10002 to rdx
mulx r11, r10, [ rsi + 0x28 ]; x48, x47<- arg1[5] * x10002
mov r9, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x100 ], r15; spilling x459 to mem
mov [ rsp + 0x108 ], r13; spilling x458 to mem
mulx r15, r13, [ rbx + 0x0 ]; x128, x127<- arg1[2] * arg2[0]
mov [ rsp + 0x110 ], r15; spilling x128 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r10
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, r15, [ rsp + 0x28 ]; x56, x55<- arg1[4] * x10001
adcx rbp, rax
clc;
adcx rcx, r15
adox r11, rbp
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0xd8 ]
adcx r10, r11
adox r10, [ rsp + 0xd0 ]
test al, al
adox rcx, r13
adcx rcx, [ rsp + 0xe8 ]
mov rdx, r12; x10003 to rdx
mulx r12, r13, [ rsi + 0x38 ]; x24, x23<- arg1[7] * x10003
adox r10, [ rsp + 0x110 ]
mov r15, rdx; preserving value of x10003 into a new reg
mov rdx, [ rbx + 0x10 ]; saving arg2[2] in rdx.
mulx rbp, r11, [ rsi + 0x8 ]; x140, x139<- arg1[1] * arg2[2]
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x118 ], rbp; spilling x140 to mem
mulx rax, rbp, [ rbx + 0x0 ]; x114, x113<- arg1[3] * arg2[0]
adcx r10, [ rsp + 0xe0 ]
mov rdx, r9; x10002 to rdx
mov [ rsp + 0x120 ], r11; spilling x139 to mem
mulx r9, r11, [ rsi + 0x30 ]; x36, x35<- arg1[6] * x10002
mov [ rsp + 0x128 ], rax; spilling x114 to mem
mov rax, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x130 ], rbp; spilling x113 to mem
mov [ rsp + 0x138 ], r9; spilling x36 to mem
mulx rbp, r9, [ rsp + 0x28 ]; x46, x45<- arg1[5] * x10001
adox r10, [ rsp + 0xf0 ]
add rcx, [ rsp + 0x108 ]; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x140 ], rbp; spilling x46 to mem
mulx rdi, rbp, rdi; x10, x9<- arg1[8] * x10004
test al, al
adox rbp, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x148 ], r10; spilling x463 to mem
mulx r13, r10, [ rsp + 0x50 ]; x54, x53<- arg1[4] * x10000
adox r12, rdi
adcx rbp, r11
mov rdx, [ rbx + 0x18 ]; arg2[3] to rdx
mulx r11, rdi, [ rsi + 0x0 ]; x156, x155<- arg1[0] * arg2[3]
mov [ rsp + 0x150 ], r11; spilling x156 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r9
mov r9, [ rsp + 0x148 ]; load m64 x463 to register64
setc r11b; spill CF x363 to reg (r11)
mov [ rsp + 0x158 ], rdi; spilling x155 to mem
seto dil; spill OF x367 to reg (rdi)
mov [ rsp + 0x160 ], r13; spilling x54 to mem
mov r13, rcx; x465, copying x461 here, cause x461 is needed in a reg for other than x465, namely all: , x465, x467, size: 2
shrd r13, r9, 58; x465 <- x463||x461 >> 58
shr r9, 58; x466 <- x463>> 58
sar  r11b, 1
adcx r12, [ rsp + 0x138 ]
adox rbp, r10
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r10, r11, [ rbx + 0x8 ]; x126, x125<- arg1[2] * arg2[1]
movzx rdi, dil
lea r12, [ rdi + r12 ]
mov rdi, [ rsp + 0x140 ]
lea r12, [rdi+r12]
clc;
adcx rbp, [ rsp + 0x130 ]
adox r12, [ rsp + 0x160 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x168 ], r9; spilling x466 to mem
mulx rdi, r9, [ rbx + 0x18 ]; x138, x137<- arg1[1] * arg2[3]
mov [ rsp + 0x170 ], rdi; spilling x138 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r11
adcx r12, [ rsp + 0x128 ]
adox r10, r12
mov rdx, [ rbx + 0x20 ]; arg2[4] to rdx
mulx r11, r12, [ rsi + 0x0 ]; x154, x153<- arg1[0] * arg2[4]
xor rdi, rdi
adox rbp, [ rsp + 0x120 ]
adox r10, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r15, rdi, r15; x8, x7<- arg1[8] * x10003
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x178 ], r14; spilling x191 to mem
mov [ rsp + 0x180 ], r11; spilling x154 to mem
mulx r14, r11, [ rsi + 0x20 ]; x102, x101<- arg1[4] * arg2[0]
mov [ rsp + 0x188 ], r12; spilling x153 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r13
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mulx r13, r12, [ rsi + 0x10 ]; x124, x123<- arg1[2] * arg2[2]
adcx r10, [ rsp + 0x150 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x190 ], r9; spilling x137 to mem
mov [ rsp + 0x198 ], r13; spilling x124 to mem
mulx r9, r13, rax; x22, x21<- arg1[7] * x10002
adox r10, [ rsp + 0x168 ]
test al, al
adox rdi, r13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1a0 ], r12; spilling x123 to mem
mulx r13, r12, [ rsp + 0x28 ]; x34, x33<- arg1[6] * x10001
adox r9, r15
adcx rdi, r12
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r15, r12, [ rsp + 0x50 ]; x44, x43<- arg1[5] * x10000
adcx r13, r9
mov r9, rbp; x472, copying x468 here, cause x468 is needed in a reg for other than x472, namely all: , x474, x472, size: 2
shrd r9, r10, 58; x472 <- x470||x468 >> 58
add rdi, r12; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, r11
adcx r15, r13
mov rdx, [ rbx + 0x8 ]; arg2[1] to rdx
mulx r11, r13, [ rsi + 0x18 ]; x112, x111<- arg1[3] * arg2[1]
adox r14, r15
shr r10, 58; x473 <- x470>> 58
add rdi, r13; could be done better, if r0 has been u8 as well
adcx r11, r14
add rdi, [ rsp + 0x1a0 ]; could be done better, if r0 has been u8 as well
adcx r11, [ rsp + 0x198 ]
mov rdx, [ rbx + 0x8 ]; arg2[1] to rdx
mulx r15, r13, [ rsi + 0x20 ]; x100, x99<- arg1[4] * arg2[1]
xor r14, r14
adox rdi, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r12, [ rbx + 0x20 ]; x136, x135<- arg1[1] * arg2[4]
adcx rdi, [ rsp + 0x188 ]
adox r11, [ rsp + 0x170 ]
adcx r11, [ rsp + 0x180 ]
test al, al
adox rdi, r9
adox r10, r11
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mulx r9, r11, [ rsi + 0x28 ]; x92, x91<- arg1[5] * arg2[0]
mov [ rsp + 0x1a8 ], r14; spilling x136 to mem
mov r14, 0x3ffffffffffffff ; moving imm to reg
and r8, r14; x460 <- x454&0x3ffffffffffffff
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1b0 ], r8; spilling x460 to mem
mulx r14, r8, [ rsp + 0x50 ]; x32, x31<- arg1[6] * x10000
mov [ rsp + 0x1b8 ], r12; spilling x135 to mem
mov r12, rdi; x479, copying x475 here, cause x475 is needed in a reg for other than x479, namely all: , x479, x481, size: 2
shrd r12, r10, 58; x479 <- x477||x475 >> 58
shr r10, 58; x480 <- x477>> 58
mov [ rsp + 0x1c0 ], r10; spilling x480 to mem
mov r10, 0x3ffffffffffffff ; moving imm to reg
and rdi, r10; x481 <- x475&0x3ffffffffffffff
mov rdx, rax; x10002 to rdx
mulx rdx, rax, [ rsi + 0x40 ]; x6, x5<- arg1[8] * x10002
mov r10, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x1c8 ], rdi; spilling x481 to mem
mov [ rsp + 0x1d0 ], r12; spilling x479 to mem
mulx rdi, r12, [ rsp + 0x28 ]; x20, x19<- arg1[7] * x10001
adox rax, r12
adcx rax, r8
mov rdx, [ rbx + 0x18 ]; arg2[3] to rdx
mulx r8, r12, [ rsi + 0x10 ]; x122, x121<- arg1[2] * arg2[3]
adox rdi, r10
adcx r14, rdi
test al, al
adox rax, r11
adcx rax, r13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r11, [ rbx + 0x10 ]; x110, x109<- arg1[3] * arg2[2]
adox r9, r14
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, rdi, [ rbx + 0x28 ]; x152, x151<- arg1[0] * arg2[5]
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r11
seto r11b; spill OF x311 to reg (r11)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, r12
adcx r15, r9
movzx r11, r11b
lea r13, [ r13 + r15 ]
lea r13, [ r13 + r11 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r12, r9, [ rsp + 0x50 ]; x18, x17<- arg1[7] * x10000
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r11, r15, [ rsp + 0x28 ]; x4, x3<- arg1[8] * x10001
adox r8, r13
mov rdx, [ rbx + 0x28 ]; arg2[5] to rdx
mulx r13, r14, [ rsi + 0x8 ]; x134, x133<- arg1[1] * arg2[5]
mov [ rsp + 0x1d8 ], r13; spilling x134 to mem
xor r13, r13
adox rax, [ rsp + 0x1b8 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1e0 ], r14; spilling x133 to mem
mulx r13, r14, [ rbx + 0x8 ]; x90, x89<- arg1[5] * arg2[1]
adcx rax, rdi
adox r8, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1e8 ], r13; spilling x90 to mem
mulx rdi, r13, [ rbx + 0x30 ]; x150, x149<- arg1[0] * arg2[6]
mov [ rsp + 0x1f0 ], rdi; spilling x150 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, [ rsp + 0x1d0 ]
adcx r10, r8
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mulx r8, rdi, [ rsi + 0x30 ]; x84, x83<- arg1[6] * arg2[0]
adox r10, [ rsp + 0x1c0 ]
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x1f8 ], r13; spilling x149 to mem
mov [ rsp + 0x200 ], r14; spilling x89 to mem
mulx r13, r14, [ rsi + 0x20 ]; x98, x97<- arg1[4] * arg2[2]
mov [ rsp + 0x208 ], r13; spilling x98 to mem
mov r13, rax; x486, copying x482 here, cause x482 is needed in a reg for other than x486, namely all: , x486, x488, size: 2
shrd r13, r10, 58; x486 <- x484||x482 >> 58
add r15, r9; could be done better, if r0 has been u8 as well
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rdi
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, r9, [ rbx + 0x18 ]; x108, x107<- arg1[3] * arg2[3]
adcx r12, r11
adox r8, r12
shr r10, 58; x487 <- x484>> 58
add r15, [ rsp + 0x200 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x1e8 ]
mov rdx, [ rbx + 0x20 ]; arg2[4] to rdx
mulx r11, r12, [ rsi + 0x10 ]; x120, x119<- arg1[2] * arg2[4]
mov [ rsp + 0x210 ], r10; spilling x487 to mem
xor r10, r10
adox r15, r14
mov rdx, [ rbx + 0x38 ]; arg2[7] to rdx
mulx r14, r10, [ rsi + 0x0 ]; x148, x147<- arg1[0] * arg2[7]
adox r8, [ rsp + 0x208 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x218 ], r14; spilling x148 to mem
mov [ rsp + 0x220 ], r10; spilling x147 to mem
mulx r14, r10, [ rbx + 0x0 ]; x78, x77<- arg1[7] * arg2[0]
adcx r15, r9
adcx rdi, r8
xor r9, r9
adox r15, r12
adox r11, rdi
adcx r15, [ rsp + 0x1e0 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r8, [ rbx + 0x30 ]; x132, x131<- arg1[1] * arg2[6]
adcx r11, [ rsp + 0x1d8 ]
xor rdi, rdi
adox r15, [ rsp + 0x1f8 ]
adox r11, [ rsp + 0x1f0 ]
adcx r15, r13
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mulx r9, r13, [ rsp + 0x50 ]; x2, x1<- arg1[8] * x10000
mov rdi, 0x3ffffffffffffff ; moving imm to reg
mov [ rsp + 0x228 ], r12; spilling x132 to mem
setc r12b; spill CF x490 to reg (r12)
mov [ rsp + 0x230 ], r8; spilling x131 to mem
mov r8, r15; x495, copying x489 here, cause x489 is needed in a reg for other than x495, namely all: , x493, x495, size: 2
and r8, rdi; x495 <- x489&0x3ffffffffffffff
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x238 ], r8; spilling x495 to mem
mulx rdi, r8, [ rsi + 0x28 ]; x88, x87<- arg1[5] * arg2[2]
adox r13, r10
adox r14, r9
mov r10, 0x3ffffffffffffff ; moving imm to reg
mov r9, [ rsp + 0x178 ]; x197, copying x191 here, cause x191 is needed in a reg for other than x197, namely all: , x197, size: 1
and r9, r10; x197 <- x191&0x3ffffffffffffff
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x240 ], r9; spilling x197 to mem
mulx r10, r9, [ rbx + 0x8 ]; x82, x81<- arg1[6] * arg2[1]
adox r13, r9
movzx r12, r12b
lea r11, [ r12 + r11 ]
adcx r11, [ rsp + 0x210 ]
adox r10, r14
mov rdx, [ rbx + 0x28 ]; arg2[5] to rdx
mulx r12, r14, [ rsi + 0x10 ]; x118, x117<- arg1[2] * arg2[5]
shrd r15, r11, 58; x493 <- x491||x489 >> 58
mov rdx, [ rsi + 0x40 ]; arg1[8] to rdx
mov [ rsp + 0x248 ], r15; spilling x493 to mem
mulx r9, r15, [ rbx + 0x0 ]; x74, x73<- arg1[8] * arg2[0]
mov [ rsp + 0x250 ], r9; spilling x74 to mem
xor r9, r9
adox r13, r8
adox rdi, r10
mov rdx, [ rbx + 0x18 ]; arg2[3] to rdx
mulx r8, r10, [ rsi + 0x20 ]; x96, x95<- arg1[4] * arg2[3]
mov rdx, [ rbx + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x258 ], r15; spilling x73 to mem
mulx r9, r15, [ rsi + 0x18 ]; x106, x105<- arg1[3] * arg2[4]
adcx r13, r10
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r15
adcx r8, rdi
clc;
adcx r13, r14
setc r14b; spill CF x251 to reg (r14)
clc;
adcx r13, [ rsp + 0x230 ]
seto dil; spill OF x247 to reg (rdi)
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, [ rsp + 0x220 ]
setc r15b; spill CF x255 to reg (r15)
seto r10b; spill OF x259 to reg (r10)
shr r11, 58; x494 <- x491>> 58
sar  dil, 1
adcx r9, r8
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx rdi, r8, [ rbx + 0x8 ]; x76, x75<- arg1[7] * arg2[1]
sar  r14b, 1
adcx r12, r9
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mulx r14, r9, [ rsi + 0x30 ]; x80, x79<- arg1[6] * arg2[2]
sar  r15b, 1
adcx r12, [ rsp + 0x228 ]
sar  r10b, 1
adcx r12, [ rsp + 0x218 ]
adox r13, [ rsp + 0x248 ]
adox r11, r12
mov rdx, [ rbx + 0x38 ]; arg2[7] to rdx
mulx r15, r10, [ rsi + 0x8 ]; x130, x129<- arg1[1] * arg2[7]
add r8, [ rsp + 0x258 ]; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r12, [ rbx + 0x40 ]; x146, x145<- arg1[0] * arg2[8]
mov [ rsp + 0x260 ], r9; spilling x146 to mem
setc r9b; spill CF x199 to reg (r9)
mov [ rsp + 0x268 ], r15; spilling x130 to mem
seto r15b; spill OF x203 to reg (r15)
mov [ rsp + 0x270 ], r12; spilling x145 to mem
mov r12, r13; x500, copying x496 here, cause x496 is needed in a reg for other than x500, namely all: , x502, x500, size: 2
shrd r12, r11, 58; x500 <- x498||x496 >> 58
sar  r9b, 1
adcx rdi, [ rsp + 0x250 ]
sar  r15b, 1
adcx r14, rdi
mov rdx, [ rbx + 0x28 ]; arg2[5] to rdx
mulx r9, r15, [ rsi + 0x18 ]; x104, x103<- arg1[3] * arg2[5]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x278 ], r12; spilling x500 to mem
mulx rdi, r12, [ rbx + 0x18 ]; x86, x85<- arg1[5] * arg2[3]
adox r8, r12
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x280 ], r10; spilling x129 to mem
mulx r12, r10, [ rbx + 0x20 ]; x94, x93<- arg1[4] * arg2[4]
adox rdi, r14
add r8, r10; could be done better, if r0 has been u8 as well
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r8, r15
adcx r12, rdi
adox r9, r12
shr r11, 58; x501 <- x498>> 58
mov r15, 0x3ffffffffffffff ; moving imm to reg
and rcx, r15; x467 <- x461&0x3ffffffffffffff
mov rdx, [ rbx + 0x30 ]; arg2[6] to rdx
mulx r10, rdi, [ rsi + 0x10 ]; x116, x115<- arg1[2] * arg2[6]
adox r8, rdi
adcx r8, [ rsp + 0x280 ]
adox r10, r9
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, [ rsp + 0x270 ]
adcx r10, [ rsp + 0x268 ]
adox r10, [ rsp + 0x260 ]
test al, al
adox r8, [ rsp + 0x278 ]
adox r11, r10
mov r12, r11; x508, copying x505 here, cause x505 is needed in a reg for other than x508, namely all: , x508, x507, size: 2
shr r12, 57; x508 <- x505>> 57
mov r9, r8; x507, copying x503 here, cause x503 is needed in a reg for other than x507, namely all: , x509, x507, size: 2
shrd r9, r11, 57; x507 <- x505||x503 >> 57
test al, al
adox r9, [ rsp + 0x240 ]
mov rdi, [ rsp + 0x0 ]; load m64 out1 to register64
mov r10, [ rsp + 0x1c8 ]; TMP = x481
mov [ rdi + 0x20 ], r10; out1[4] = TMP
adox r12, r14
mov r10, r9; x513, copying x510 here, cause x510 is needed in a reg for other than x513, namely all: , x514, x513, size: 2
shrd r10, r12, 58; x513 <- x512||x510 >> 58
and r13, r15; x502 <- x496&0x3ffffffffffffff
add r10, [ rsp + 0x1b0 ]
mov r11, r10; x516, copying x515 here, cause x515 is needed in a reg for other than x516, namely all: , x516, x517, size: 2
shr r11, 58; x516 <- x515>> 58
and r10, r15; x517 <- x515&0x3ffffffffffffff
and r9, r15; x514 <- x510&0x3ffffffffffffff
mov r12, [ rsp + 0x238 ]; TMP = x495
mov [ rdi + 0x30 ], r12; out1[6] = TMP
and rbp, r15; x474 <- x468&0x3ffffffffffffff
lea r11, [ r11 + rcx ]
mov r12, 0x1ffffffffffffff ; moving imm to reg
and r8, r12; x509 <- x503&0x1ffffffffffffff
mov [ rdi + 0x0 ], r9; out1[0] = x514
and rax, r15; x488 <- x482&0x3ffffffffffffff
mov [ rdi + 0x28 ], rax; out1[5] = x488
mov [ rdi + 0x18 ], rbp; out1[3] = x474
mov [ rdi + 0x38 ], r13; out1[7] = x502
mov [ rdi + 0x8 ], r10; out1[1] = x517
mov [ rdi + 0x10 ], r11; out1[2] = x518
mov [ rdi + 0x40 ], r8; out1[8] = x509
mov rbx, [ rsp + 0x288 ]; restoring from stack
mov rbp, [ rsp + 0x290 ]; restoring from stack
mov r12, [ rsp + 0x298 ]; restoring from stack
mov r13, [ rsp + 0x2a0 ]; restoring from stack
mov r14, [ rsp + 0x2a8 ]; restoring from stack
mov r15, [ rsp + 0x2b0 ]; restoring from stack
add rsp, 0x2b8 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 228.31, best 132.11428571428573, lastGood 133.57142857142858
; seed 3179949323651885 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3879815 ms / 60000 runs=> 64.66358333333334ms/run
; Time spent for assembling and measureing (initial batch_size=71, initial num_batches=101): 189144 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.048750778065448995
; number reverted permutation/ tried permutation: 20044 / 29868 =67.109%
; number reverted decision/ tried decision: 18786 / 30133 =62.344%