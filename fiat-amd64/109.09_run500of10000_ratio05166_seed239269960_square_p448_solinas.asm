SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x360 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x330 ], rbx; saving to stack
mov [ rsp + 0x338 ], rbp; saving to stack
mov [ rsp + 0x340 ], r12; saving to stack
mov [ rsp + 0x348 ], r13; saving to stack
mov [ rsp + 0x350 ], r14; saving to stack
mov [ rsp + 0x358 ], r15; saving to stack
imul rax, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
imul r10, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov rdx, rax; x19 to rdx
mulx rax, r11, [ rsi + 0x0 ]; x127, x126<- arg1[0] * x19
mov rbx, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, r12, r10; x115, x114<- arg1[1] * x20
mov r13, [ rsi + 0x38 ]; load m64 x2 to register64
imul r14, r13, 0x2; x4 <- x2 * 0x2
mov r15, [ rsi + 0x30 ]; load m64 x7 to register64
mov rdx, r14; x4 to rdx
mulx r14, rcx, [ rsi + 0x20 ]; x55, x54<- arg1[4] * x4
imul r8, r15, 0x2; x9 <- x7 * 0x2
mov r9, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rbx; spilling x19 to mem
mulx rdi, rbx, r8; x47, x46<- arg1[5] * x9
test al, al
adox rbx, rcx
adcx rbx, r12
adox r14, rdi
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r11
adcx rbp, r14
adox rax, rbp
mov r11, rbx; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd r11, rax, 56; x146 <- x144||x142 >> 56
imul r12, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
mov rdx, r12; x18 to rdx
mulx r12, rcx, [ rsi + 0x0 ]; x125, x124<- arg1[0] * x18
mov rdi, rdx; preserving value of x18 into a new reg
mov rdx, [ rsp + 0x8 ]; saving x19 in rdx.
mulx r14, rbp, [ rsi + 0x8 ]; x113, x112<- arg1[1] * x19
mov rax, [ rsi + 0x38 ]; load m64 x1 to register64
mov [ rsp + 0x10 ], r10; spilling x20 to mem
imul r10, rax, 0x2; x3 <- x1 * 0x2
mov [ rsp + 0x18 ], r13; spilling x2 to mem
mov r13, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x20 ], r12; spilling x125 to mem
mov [ rsp + 0x28 ], r14; spilling x113 to mem
mulx r12, r14, r10; x105, x104<- arg1[1] * x3
mov rdx, [ rsi + 0x30 ]; load m64 x6 to register64
mov [ rsp + 0x30 ], r12; spilling x105 to mem
mov r12, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x38 ], r11; spilling x146 to mem
mov [ rsp + 0x40 ], rcx; spilling x124 to mem
mulx r11, rcx, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
imul rdx, r12, 0x2; x8 <- x6 * 0x2
mov [ rsp + 0x48 ], r8; spilling x9 to mem
mov [ rsp + 0x50 ], r11; spilling x101 to mem
mulx r8, r11, [ rsi + 0x10 ]; x93, x92<- arg1[2] * x8
mov [ rsp + 0x58 ], r8; spilling x93 to mem
mov r8, [ rsi + 0x28 ]; load m64 x11 to register64
mov [ rsp + 0x60 ], rbp; spilling x112 to mem
imul rbp, r8, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x68 ], r14; spilling x104 to mem
mov r14, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x70 ], rcx; spilling x100 to mem
mov [ rsp + 0x78 ], r11; spilling x92 to mem
mulx rcx, r11, rbp; x81, x80<- arg1[3] * x13
mov rdx, [ rsi + 0x20 ]; load m64 x16 to register64
mov [ rsp + 0x80 ], rcx; spilling x81 to mem
mulx rdx, rcx, [ rsi + 0x20 ]; x69, x68<- arg1[4] * x16
xchg rdx, r9; x4, swapping with x69, which is currently in rdx
mov [ rsp + 0x88 ], r9; spilling x69 to mem
mov [ rsp + 0x90 ], r11; spilling x80 to mem
mulx r9, r11, [ rsi + 0x28 ]; x45, x44<- arg1[5] * x4
mov [ rsp + 0x98 ], r9; spilling x45 to mem
mov r9, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xa0 ], rcx; spilling x68 to mem
mulx r15, rcx, r15; x43, x42<- arg1[6] * x7
mov rdx, r10; x3 to rdx
mov [ rsp + 0xa8 ], r15; spilling x43 to mem
mulx r10, r15, [ rsi + 0x28 ]; x37, x36<- arg1[5] * x3
xchg rdx, r12; x6, swapping with x3, which is currently in rdx
mov [ rsp + 0xb0 ], r10; spilling x37 to mem
mov [ rsp + 0xb8 ], r11; spilling x44 to mem
mulx r10, r11, [ rsi + 0x30 ]; x35, x34<- arg1[6] * x6
test al, al
adox r11, r15
adcx r11, rcx
seto cl; spill OF x229 to reg (rcx)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0xb8 ]
seto r15b; spill OF x237 to reg (r15)
mov [ rsp + 0xc0 ], r10; spilling x35 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0xa0 ]
setc r10b; spill CF x233 to reg (r10)
clc;
adcx r11, [ rsp + 0x90 ]
mov byte [ rsp + 0xc8 ], r15b; spilling byte x237 to mem
seto r15b; spill OF x241 to reg (r15)
mov byte [ rsp + 0xd0 ], r10b; spilling byte x233 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x78 ]
seto r10b; spill OF x249 to reg (r10)
mov byte [ rsp + 0xd8 ], r15b; spilling byte x241 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x70 ]
setc r15b; spill CF x245 to reg (r15)
clc;
adcx r11, [ rsp + 0x68 ]
mov byte [ rsp + 0xe0 ], r10b; spilling byte x249 to mem
seto r10b; spill OF x253 to reg (r10)
mov byte [ rsp + 0xe8 ], r15b; spilling byte x245 to mem
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x60 ]
setc r15b; spill CF x257 to reg (r15)
clc;
adcx r11, [ rsp + 0x40 ]
mov [ rsp + 0xf0 ], rbx; spilling x142 to mem
mov rbx, [ rsp + 0xb0 ]; load m64 x37 to register64
movzx rcx, cl
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0xc0 ]
lea rbx, [rcx+rbx]
movzx rcx, byte [ rsp + 0xd0 ]; load byte memx233 to register64
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0xa8 ]
lea rbx, [rcx+rbx]
movzx rcx, byte [ rsp + 0xc8 ]; load byte memx237 to register64
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0x98 ]
lea rbx, [rcx+rbx]
setc cl; spill CF x265 to reg (rcx)
clc;
adcx r11, [ rsp + 0x38 ]
mov [ rsp + 0xf8 ], r11; spilling x328 to mem
movzx r11, byte [ rsp + 0xd8 ]; load byte memx241 to register64
lea rbx, [ r11 + rbx ]
mov r11, [ rsp + 0x88 ]
lea rbx, [r11+rbx]
movzx r11, byte [ rsp + 0xe8 ]; load byte memx245 to register64
lea rbx, [ r11 + rbx ]
mov r11, [ rsp + 0x80 ]
lea rbx, [r11+rbx]
movzx r11, byte [ rsp + 0xe0 ]; load byte memx249 to register64
lea rbx, [ r11 + rbx ]
mov r11, [ rsp + 0x58 ]
lea rbx, [r11+rbx]
movzx r10, r10b
lea rbx, [ r10 + rbx ]
mov r10, [ rsp + 0x50 ]
lea rbx, [r10+rbx]
movzx r15, r15b
lea rbx, [ r15 + rbx ]
mov r15, [ rsp + 0x30 ]
lea rbx, [r15+rbx]
adox rbx, [ rsp + 0x28 ]
movzx rcx, cl
lea rbx, [ rcx + rbx ]
mov rcx, [ rsp + 0x20 ]
lea rbx, [rcx+rbx]
adc rbx, 0x0
mov r11, 0x38 ; moving imm to reg
bzhi r11, [ rsp + 0xf0 ], r11; x147 <- x142 (only least 0x38 bits)
imul r10, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
imul r15, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
mov rcx, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x100 ], r11; spilling x147 to mem
mulx r10, r11, r10; x119, x118<- arg1[0] * x5
imul rdx, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
mov [ rsp + 0x108 ], r15; spilling x21 to mem
imul r15, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov [ rsp + 0x110 ], rax; spilling x1 to mem
mov rax, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x8 ], r13; spilling x19 to mem
mov [ rsp + 0x118 ], rbx; spilling x330 to mem
mulx r13, rbx, rdi; x83, x82<- arg1[3] * x18
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x120 ], r10; spilling x119 to mem
mov [ rsp + 0x128 ], r13; spilling x83 to mem
mulx r10, r13, rax; x107, x106<- arg1[1] * x10
mov rdx, r15; x15 to rdx
mov [ rsp + 0x130 ], r10; spilling x107 to mem
mulx r15, r10, [ rsi + 0x10 ]; x95, x94<- arg1[2] * x15
mov [ rsp + 0x138 ], r15; spilling x95 to mem
mov r15, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x140 ], r11; spilling x118 to mem
mov [ rsp + 0x148 ], r13; spilling x106 to mem
mulx r11, r13, r12; x57, x56<- arg1[4] * x3
mov rdx, r14; x8 to rdx
mov [ rsp + 0x150 ], r11; spilling x57 to mem
mulx r14, r11, [ rsi + 0x28 ]; x49, x48<- arg1[5] * x8
test al, al
adox r11, r13
adcx r11, rbx
seto bl; spill OF x149 to reg (rbx)
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r10
setc r10b; spill CF x153 to reg (r10)
clc;
adcx r11, [ rsp + 0x148 ]
seto r13b; spill OF x157 to reg (r13)
mov byte [ rsp + 0x158 ], r10b; spilling byte x153 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x140 ]
movzx rbx, bl
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x150 ]
lea r14, [rbx+r14]
movzx rbx, byte [ rsp + 0x158 ]; load byte memx153 to register64
lea r14, [ rbx + r14 ]
mov rbx, [ rsp + 0x128 ]
lea r14, [rbx+r14]
movzx r13, r13b
lea r14, [ r13 + r14 ]
mov r13, [ rsp + 0x138 ]
lea r14, [r13+r14]
adcx r14, [ rsp + 0x130 ]
adox r14, [ rsp + 0x120 ]
mov rbx, r11; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x331, x332, size: 2
shrd rbx, r14, 56; x331 <- x166||x164 >> 56
mov r13, rbx; x333, copying x331 here, cause x331 is needed in a reg for other than x333, namely all: , x333--x334, x338--x339, size: 2
xor r14, r14
adox r13, [ rsp + 0xf8 ]
mov r14, [ rsp + 0x118 ]; x335, copying x330 here, cause x330 is needed in a reg for other than x335, namely all: , x335, size: 1
mov r10, 0x0 ; moving imm to reg
adox r14, r10
mov r10, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x160 ], r8; spilling x11 to mem
mov [ rsp + 0x168 ], rbp; spilling x13 to mem
mulx r8, rbp, r15; x123, x122<- arg1[0] * x15
mov rdx, r13; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x336, x337, size: 2
shrd rdx, r14, 56; x336 <- x335||x333 >> 56
mov r14, rdx; preserving value of x336 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x170 ], r8; spilling x123 to mem
mov [ rsp + 0x178 ], rbp; spilling x122 to mem
mulx r8, rbp, rdi; x111, x110<- arg1[1] * x18
mov rdx, [ rsp + 0x8 ]; x19 to rdx
mov [ rsp + 0x180 ], r8; spilling x111 to mem
mulx rdx, r8, [ rsi + 0x10 ]; x99, x98<- arg1[2] * x19
xchg rdx, r10; x8, swapping with x99, which is currently in rdx
mov [ rsp + 0x188 ], r10; spilling x99 to mem
mov [ rsp + 0x190 ], r14; spilling x336 to mem
mulx r10, r14, [ rsi + 0x18 ]; x77, x76<- arg1[3] * x8
mov [ rsp + 0x198 ], r10; spilling x77 to mem
mov r10, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x1a0 ], rbp; spilling x110 to mem
mov [ rsp + 0x1a8 ], r8; spilling x98 to mem
mulx rbp, r8, [ rsp + 0x168 ]; x65, x64<- arg1[4] * x13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1b0 ], rbp; spilling x65 to mem
mov [ rsp + 0x1b8 ], r14; spilling x76 to mem
mulx rbp, r14, r12; x89, x88<- arg1[2] * x3
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1c0 ], rbp; spilling x89 to mem
mov [ rsp + 0x1c8 ], r14; spilling x88 to mem
mulx rbp, r14, r9; x41, x40<- arg1[6] * x4
mov rdx, r12; x3 to rdx
mov [ rsp + 0x1d0 ], rbp; spilling x41 to mem
mulx r12, rbp, [ rsi + 0x30 ]; x33, x32<- arg1[6] * x3
test al, al
adox rbp, r14
adcx rbp, r8
setc r8b; spill CF x205 to reg (r8)
clc;
adcx rbp, [ rsp + 0x1b8 ]
seto r14b; spill OF x201 to reg (r14)
mov byte [ rsp + 0x1d8 ], r8b; spilling byte x205 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x1c8 ]
setc r8b; spill CF x209 to reg (r8)
clc;
adcx rbp, [ rsp + 0x1a8 ]
mov byte [ rsp + 0x1e0 ], r8b; spilling byte x209 to mem
seto r8b; spill OF x213 to reg (r8)
mov [ rsp + 0x1e8 ], r12; spilling x33 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x1a0 ]
setc r12b; spill CF x217 to reg (r12)
clc;
adcx rbp, [ rsp + 0x178 ]
mov [ rsp + 0x1f0 ], rcx; spilling x6 to mem
setc cl; spill CF x225 to reg (rcx)
clc;
adcx rbp, [ rsp + 0x190 ]
mov [ rsp + 0x1f8 ], rbp; spilling x341 to mem
mov rbp, [ rsp + 0x1e8 ]; load m64 x33 to register64
movzx r14, r14b
lea rbp, [ r14 + rbp ]
mov r14, [ rsp + 0x1d0 ]
lea rbp, [r14+rbp]
movzx r14, byte [ rsp + 0x1d8 ]; load byte memx205 to register64
lea rbp, [ r14 + rbp ]
mov r14, [ rsp + 0x1b0 ]
lea rbp, [r14+rbp]
movzx r14, byte [ rsp + 0x1e0 ]; load byte memx209 to register64
lea rbp, [ r14 + rbp ]
mov r14, [ rsp + 0x198 ]
lea rbp, [r14+rbp]
movzx r8, r8b
lea rbp, [ r8 + rbp ]
mov r8, [ rsp + 0x1c0 ]
lea rbp, [r8+rbp]
movzx r12, r12b
lea rbp, [ r12 + rbp ]
mov r12, [ rsp + 0x188 ]
lea rbp, [r12+rbp]
adox rbp, [ rsp + 0x180 ]
movzx rcx, cl
lea rbp, [ rcx + rbp ]
mov rcx, [ rsp + 0x170 ]
lea rbp, [rcx+rbp]
mov r14, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rax, r8, rax; x121, x120<- arg1[0] * x10
adc rbp, 0x0
mov rdx, [ rsp + 0x1f8 ]; load m64 x341 to register64
mov r12, rdx; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd r12, rbp, 56; x349 <- x343||x341 >> 56
mov rcx, rdx; preserving value of x341 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rdi, rbp, rdi; x97, x96<- arg1[2] * x18
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x200 ], rax; spilling x121 to mem
mulx r15, rax, r15; x109, x108<- arg1[1] * x15
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x208 ], r15; spilling x109 to mem
mov [ rsp + 0x210 ], rdi; spilling x97 to mem
mulx r15, rdi, r14; x73, x72<- arg1[3] * x3
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x218 ], r15; spilling x73 to mem
mov [ rsp + 0x220 ], r12; spilling x349 to mem
mulx r15, r12, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
mov rdx, r10; x8 to rdx
mulx rdx, r10, [ rsi + 0x20 ]; x61, x60<- arg1[4] * x8
mov [ rsp + 0x228 ], r15; spilling x85 to mem
mov r15, rdx; preserving value of x61 into a new reg
mov rdx, [ rsp + 0x160 ]; saving x11 in rdx.
mov [ rsp + 0x230 ], r8; spilling x120 to mem
mulx rdx, r8, [ rsi + 0x28 ]; x53, x52<- arg1[5] * x11
mov [ rsp + 0x238 ], r15; spilling x61 to mem
mov r15, rdx; preserving value of x53 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x240 ], rax; spilling x108 to mem
mov [ rsp + 0x248 ], rbp; spilling x96 to mem
mulx rax, rbp, [ rsp + 0x110 ]; x31, x30<- arg1[7] * x1
mov rdx, [ rsp + 0x18 ]; x2 to rdx
mov [ rsp + 0x250 ], r15; spilling x53 to mem
mulx rdx, r15, [ rsi + 0x38 ]; x39, x38<- arg1[7] * x2
add rbp, r15; could be done better, if r0 has been u8 as well
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r8
setc r8b; spill CF x169 to reg (r8)
clc;
adcx rbp, r10
setc r10b; spill CF x177 to reg (r10)
clc;
adcx rbp, rdi
seto dil; spill OF x173 to reg (rdi)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbp, r12
seto r12b; spill OF x185 to reg (r12)
mov byte [ rsp + 0x258 ], r10b; spilling byte x177 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, [ rsp + 0x248 ]
setc r10b; spill CF x181 to reg (r10)
clc;
adcx rbp, [ rsp + 0x240 ]
mov byte [ rsp + 0x260 ], r12b; spilling byte x185 to mem
setc r12b; spill CF x193 to reg (r12)
clc;
adcx rbp, [ rsp + 0x230 ]
mov byte [ rsp + 0x268 ], r12b; spilling byte x193 to mem
setc r12b; spill CF x197 to reg (r12)
clc;
adcx rbp, [ rsp + 0x220 ]
movzx r8, r8b
lea rdx, [ rdx + rax ]
lea rdx, [ rdx + r8 ]
movzx rdi, dil
lea rdx, [ rdi + rdx ]
mov rdi, [ rsp + 0x250 ]
lea rdx, [rdi+rdx]
movzx rax, byte [ rsp + 0x258 ]; load byte memx177 to register64
lea rdx, [ rax + rdx ]
mov rax, [ rsp + 0x238 ]
lea rdx, [rax+rdx]
movzx r10, r10b
lea rdx, [ r10 + rdx ]
mov r10, [ rsp + 0x218 ]
lea rdx, [r10+rdx]
movzx r8, byte [ rsp + 0x260 ]; load byte memx185 to register64
lea rdx, [ r8 + rdx ]
mov r8, [ rsp + 0x228 ]
lea rdx, [r8+rdx]
adox rdx, [ rsp + 0x210 ]
movzx rdi, byte [ rsp + 0x268 ]; load byte memx193 to register64
lea rdx, [ rdi + rdx ]
mov rdi, [ rsp + 0x208 ]
lea rdx, [rdi+rdx]
movzx r12, r12b
lea rdx, [ r12 + rdx ]
mov r12, [ rsp + 0x200 ]
lea rdx, [r12+rdx]
adc rdx, 0x0
mov rax, rbp; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x360, x359, size: 2
shrd rax, rdx, 56; x359 <- x353||x351 >> 56
mov r10, 0xffffffffffffff ; moving imm to reg
and r11, r10; x332 <- x164&0xffffffffffffff
lea rax, [ rax + r11 ]
mov r8, rax; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, x366, size: 2
shr r8, 56; x365 <- x361>> 56
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rdi, r12, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, r15, r9; x103, x102<- arg1[1] * x4
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x270 ], rdi; spilling x133 to mem
mulx r10, rdi, [ rsp + 0x48 ]; x91, x90<- arg1[2] * x9
mov rdx, [ rsi + 0x28 ]; load m64 x12 to register64
mov [ rsp + 0x278 ], r11; spilling x103 to mem
imul r11, rdx, 0x2; x14 <- x12 * 0x2
mov [ rsp + 0x280 ], r10; spilling x91 to mem
mov r10, [ rsi + 0x20 ]; load m64 x17 to register64
mov [ rsp + 0x288 ], r8; spilling x365 to mem
mov r8, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x290 ], r12; spilling x132 to mem
mov [ rsp + 0x298 ], r15; spilling x102 to mem
mulx r12, r15, r11; x79, x78<- arg1[3] * x14
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x2a0 ], r12; spilling x79 to mem
mulx r10, r12, r10; x67, x66<- arg1[4] * x17
mov rdx, r14; x3 to rdx
mov [ rsp + 0x2a8 ], r10; spilling x67 to mem
mulx r14, r10, [ rsi + 0x28 ]; x29, x28<- arg1[5] * x3
mov [ rsp + 0x2b0 ], r14; spilling x29 to mem
mov r14, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x2b8 ], rdi; spilling x90 to mem
mov [ rsp + 0x2c0 ], r15; spilling x78 to mem
mulx rdi, r15, [ rsp + 0x1f0 ]; x27, x26<- arg1[6] * x6
add r15, r10; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r12
seto r12b; spill OF x309 to reg (r12)
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x2c0 ]
seto r10b; spill OF x313 to reg (r10)
mov byte [ rsp + 0x2c8 ], r12b; spilling byte x309 to mem
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, [ rsp + 0x2b8 ]
seto r12b; spill OF x317 to reg (r12)
mov byte [ rsp + 0x2d0 ], r10b; spilling byte x313 to mem
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r15, [ rsp + 0x298 ]
setc r10b; spill CF x305 to reg (r10)
clc;
adcx r15, [ rsp + 0x290 ]
mov byte [ rsp + 0x2d8 ], r12b; spilling byte x317 to mem
seto r12b; spill OF x321 to reg (r12)
mov [ rsp + 0x2e0 ], rdi; spilling x27 to mem
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, r15
mov r15, 0xffffffffffffff ; moving imm to reg
setc dl; spill CF x325 to reg (rdx)
seto dil; spill OF x339 to reg (rdi)
mov byte [ rsp + 0x2e8 ], r12b; spilling byte x321 to mem
mov r12, rbx; x345, copying x338 here, cause x338 is needed in a reg for other than x345, namely all: , x345, x344, size: 2
and r12, r15; x345 <- x338&0xffffffffffffff
add r12, [ rsp + 0x288 ]
mov r15, [ rsp + 0x2b0 ]; load m64 x29 to register64
sar  r10b, 1
adcx r15, [ rsp + 0x2e0 ]
sar byte [ rsp + 0x2c8 ], 1
adcx r15, [ rsp + 0x2a8 ]
sar byte [ rsp + 0x2d0 ], 1
adcx r15, [ rsp + 0x2a0 ]
sar byte [ rsp + 0x2d8 ], 1
adcx r15, [ rsp + 0x280 ]
sar byte [ rsp + 0x2e8 ], 1
adcx r15, [ rsp + 0x278 ]
sar  dl, 1
adcx r15, [ rsp + 0x270 ]
mov r10, 0x38 ; moving imm to reg
bzhi rcx, rcx, r10; x350 <- x341 (only least 0x38 bits)
movzx rdx, dil; x340, copying x339 here, cause x339 is needed in a reg for other than x340, namely all: , x340, size: 1
lea rdx, [ rdx + r15 ]
shrd rbx, rdx, 56; x344 <- x340||x338 >> 56
mov rdx, r9; x4 to rdx
mulx r9, rdi, [ rsi + 0x10 ]; x87, x86<- arg1[2] * x4
mov r15, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x2f0 ], rcx; spilling x350 to mem
mulx r10, rcx, [ rsp + 0x108 ]; x131, x130<- arg1[0] * x21
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x2f8 ], r12; spilling x370 to mem
mov [ rsp + 0x300 ], r10; spilling x131 to mem
mulx r12, r10, [ rsp + 0x48 ]; x75, x74<- arg1[3] * x9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x308 ], r9; spilling x87 to mem
mulx r11, r9, r11; x63, x62<- arg1[4] * x14
mov rdx, r14; x3 to rdx
mulx rdx, r14, [ rsi + 0x30 ]; x25, x24<- arg1[6] * x3
add r14, r9; could be done better, if r0 has been u8 as well
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r10
seto r10b; spill OF x293 to reg (r10)
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, rdi
setc dil; spill CF x289 to reg (rdi)
clc;
adcx r14, rcx
seto cl; spill OF x297 to reg (rcx)
mov [ rsp + 0x310 ], r12; spilling x75 to mem
mov r12, -0x3 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, rbx
movzx rdi, dil
lea r11, [ r11 + rdx ]
lea r11, [ r11 + rdi ]
movzx r10, r10b
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x310 ]
lea r11, [r10+r11]
movzx rcx, cl
lea r11, [ rcx + r11 ]
mov rcx, [ rsp + 0x308 ]
lea r11, [rcx+r11]
adcx r11, [ rsp + 0x300 ]
adox r11, r9
mov rdx, [ rsp + 0x10 ]; x20 to rdx
mulx rdx, rbx, [ rsi + 0x0 ]; x129, x128<- arg1[0] * x20
mov rdi, r14; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x355, x354, size: 2
shrd rdi, r11, 56; x354 <- x348||x346 >> 56
mov r10, 0xffffffffffffff ; moving imm to reg
and rbp, r10; x360 <- x351&0xffffffffffffff
mov rcx, rdx; preserving value of x129 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, r9, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
mov rdx, r15; x4 to rdx
mulx rdx, r15, [ rsi + 0x18 ]; x71, x70<- arg1[3] * x4
mov r12, rdx; preserving value of x71 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x318 ], rbp; spilling x360 to mem
mulx r10, rbp, [ rsp + 0x48 ]; x59, x58<- arg1[4] * x9
mov rdx, r8; x12 to rdx
mulx rdx, r8, [ rsi + 0x28 ]; x51, x50<- arg1[5] * x12
mov [ rsp + 0x320 ], rcx; spilling x129 to mem
mov rcx, rdx; preserving value of x51 into a new reg
mov rdx, [ rsp + 0x110 ]; saving x1 in rdx.
mov [ rsp + 0x328 ], r11; spilling x117 to mem
mulx rdx, r11, [ rsi + 0x38 ]; x23, x22<- arg1[7] * x1
adox r11, r8
adcx r11, rbp
setc bpl; spill CF x273 to reg (rbp)
clc;
adcx r11, r15
setc r15b; spill CF x277 to reg (r15)
clc;
adcx r11, r9
seto r9b; spill OF x269 to reg (r9)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rbx
movzx r9, r9b
lea rcx, [ rcx + rdx ]
lea rcx, [ rcx + r9 ]
movzx rbp, bpl
lea r10, [ r10 + rcx ]
lea r10, [ r10 + rbp ]
setc bl; spill CF x281 to reg (rbx)
clc;
adcx r11, rdi
movzx r15, r15b
lea r12, [ r12 + r10 ]
lea r12, [ r12 + r15 ]
movzx rbx, bl
lea r12, [ rbx + r12 ]
mov rbx, [ rsp + 0x328 ]
lea r12, [rbx+r12]
adox r12, [ rsp + 0x320 ]
mov rdi, 0x38 ; moving imm to reg
setc dl; spill CF x357 to reg (rdx)
bzhi rdi, [ rsp + 0x2f8 ], rdi; x376 <- x370 (only least 0x38 bits)
movzx r9, dl; x358, copying x357 here, cause x357 is needed in a reg for other than x358, namely all: , x358, size: 1
lea r9, [ r9 + r12 ]
mov rbp, [ rsp + 0x2f8 ]; x375, copying x370 here, cause x370 is needed in a reg for other than x375, namely all: , x375, size: 1
shr rbp, 56; x375 <- x370>> 56
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x0 ], rdi; out1[0] = x376
mov rbx, r11; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x362, x363, size: 2
shrd rbx, r9, 56; x362 <- x358||x356 >> 56
mov rcx, 0x38 ; moving imm to reg
bzhi r13, r13, rcx; x337 <- x333 (only least 0x38 bits)
add r13, [ rsp + 0x288 ]
add rbx, [ rsp + 0x100 ]
mov r10, rbx; x367, copying x364 here, cause x364 is needed in a reg for other than x367, namely all: , x368, x367, size: 2
shr r10, 56; x367 <- x364>> 56
lea r10, [ r10 + r13 ]
mov rdx, r10; x372, copying x371 here, cause x371 is needed in a reg for other than x372, namely all: , x372, x373, size: 2
shr rdx, 56; x372 <- x371>> 56
add rdx, [ rsp + 0x2f0 ]
mov r12, 0xffffffffffffff ; moving imm to reg
and r10, r12; x373 <- x371&0xffffffffffffff
mov r9, [ rsp + 0x318 ]; TMP = x360
mov [ r15 + 0x30 ], r9; out1[6] = TMP
and rbx, r12; x368 <- x364&0xffffffffffffff
bzhi r14, r14, rcx; x355 <- x346 (only least 0x38 bits)
and rax, r12; x366 <- x361&0xffffffffffffff
mov [ r15 + 0x20 ], r10; out1[4] = x373
and r11, r12; x363 <- x356&0xffffffffffffff
mov [ r15 + 0x38 ], rax; out1[7] = x366
mov [ r15 + 0x10 ], r11; out1[2] = x363
lea rbp, [ rbp + r14 ]
mov [ r15 + 0x28 ], rdx; out1[5] = x374
mov [ r15 + 0x8 ], rbp; out1[1] = x377
mov [ r15 + 0x18 ], rbx; out1[3] = x368
mov rbx, [ rsp + 0x330 ]; restoring from stack
mov rbp, [ rsp + 0x338 ]; restoring from stack
mov r12, [ rsp + 0x340 ]; restoring from stack
mov r13, [ rsp + 0x348 ]; restoring from stack
mov r14, [ rsp + 0x350 ]; restoring from stack
mov r15, [ rsp + 0x358 ]; restoring from stack
add rsp, 0x360 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; clocked at 3466 MHz
; first cyclecount 109.8, best 101.01829268292683, lastGood 109.08588957055214
; seed 239269960 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; time needed: 32040 ms / 500 runs=> 64.08ms/run
; Time spent for assembling and measureing (initial batch_size=159, initial num_batches=101): 3666 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.11441947565543072
; number reverted permutation/ tried permutation: 186 / 248 =75.000%
; number reverted decision/ tried decision: 172 / 253 =67.984%