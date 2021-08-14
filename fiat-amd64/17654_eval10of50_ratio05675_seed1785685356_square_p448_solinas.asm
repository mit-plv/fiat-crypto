SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x3b0
mov rax, [ rsi + 0x38 ]; load m64 x1 to register64
mov r10, [ rsi + 0x38 ]; load m64 x2 to register64
imul r11, rax, 0x2; x3 <- x1 * 0x2
imul rdx, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
imul rcx, r10, 0x2; x4 <- x2 * 0x2
mov r8, [ rsi + 0x30 ]; load m64 x6 to register64
mov r9, [ rsi + 0x30 ]; load m64 x7 to register64
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
imul r15, r8, 0x2; x8 <- x6 * 0x2
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
imul r14, r9, 0x2; x9 <- x7 * 0x2
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
imul r13, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mov r12, [ rsi + 0x28 ]; load m64 x11 to register64
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mov rbp, [ rsi + 0x28 ]; load m64 x12 to register64
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
imul rbx, r12, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
imul rdi, rbp, 0x2; x14 <- x12 * 0x2
mov [ rsp + 0x38 ], rax; spilling x1 to mem
imul rax, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov [ rsp + 0x40 ], r10; spilling x2 to mem
mov r10, [ rsi + 0x20 ]; load m64 x16 to register64
mov [ rsp + 0x48 ], rdi; spilling x14 to mem
mov rdi, [ rsi + 0x20 ]; load m64 x17 to register64
mov [ rsp + 0x50 ], rdi; spilling x17 to mem
imul rdi, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
mov [ rsp + 0x58 ], rax; spilling x15 to mem
imul rax, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
mov [ rsp + 0x60 ], r13; spilling x10 to mem
imul r13, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov [ rsp + 0x68 ], rdx; spilling x5 to mem
imul rdx, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
mov [ rsp + 0x70 ], r8; spilling x6 to mem
mov r8, rdx; preserving value of x21 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x78 ], r9; spilling x7 to mem
mov [ rsp + 0x80 ], r10; spilling x16 to mem
mulx r9, r10, rax; x127, x126<- arg1[0] * x19
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x88 ], r8; spilling x21 to mem
mov [ rsp + 0x90 ], rbx; spilling x13 to mem
mulx r8, rbx, r13; x115, x114<- arg1[1] * x20
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x98 ], r15; spilling x8 to mem
mov [ rsp + 0xa0 ], r11; spilling x3 to mem
mulx r15, r11, rcx; x55, x54<- arg1[4] * x4
mov rdx, r14; x9 to rdx
mov [ rsp + 0xa8 ], rdi; spilling x18 to mem
mov [ rsp + 0xb0 ], r9; spilling x127 to mem
mulx rdi, r9, [ rsi + 0x28 ]; x47, x46<- arg1[5] * x9
test al, al
adox r9, r11
adcx r9, rbx
setc bl; spill CF x139 to reg (rbx)
clc;
adcx r9, r10
adox r15, rdi
movzx rbx, bl
lea r8, [ r8 + r15 ]
lea r8, [ r8 + rbx ]
adcx r8, [ rsp + 0xb0 ]
mov r10, r9; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x146, x147, size: 2
shrd r10, r8, 56; x146 <- x144||x142 >> 56
mov r11, 0x38 ; moving imm to reg
bzhi r9, r9, r11; x147 <- x142 (only least 0x38 bits)
mov rdi, rdx; preserving value of x9 into a new reg
mov rdx, [ rsp + 0xa8 ]; saving x18 in rdx.
mulx rbx, r15, [ rsi + 0x0 ]; x125, x124<- arg1[0] * x18
mov r8, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xb8 ], r9; spilling x147 to mem
mulx r11, r9, rax; x113, x112<- arg1[1] * x19
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0xc0 ], rbp; spilling x12 to mem
mov [ rsp + 0xc8 ], r12; spilling x11 to mem
mulx rbp, r12, [ rsp + 0xa0 ]; x105, x104<- arg1[1] * x3
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xd0 ], rbx; spilling x125 to mem
mov [ rsp + 0xd8 ], r11; spilling x113 to mem
mulx rbx, r11, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xe0 ], rbp; spilling x105 to mem
mov [ rsp + 0xe8 ], rbx; spilling x101 to mem
mulx rbp, rbx, [ rsp + 0x98 ]; x93, x92<- arg1[2] * x8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xf0 ], rbp; spilling x93 to mem
mov [ rsp + 0xf8 ], r10; spilling x146 to mem
mulx rbp, r10, [ rsp + 0x90 ]; x81, x80<- arg1[3] * x13
mov rdx, [ rsp + 0x80 ]; x16 to rdx
mov [ rsp + 0x100 ], rbp; spilling x81 to mem
mulx rdx, rbp, [ rsi + 0x20 ]; x69, x68<- arg1[4] * x16
mov [ rsp + 0x108 ], r15; spilling x124 to mem
mov r15, rdx; preserving value of x69 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x110 ], r9; spilling x112 to mem
mov [ rsp + 0x118 ], r12; spilling x104 to mem
mulx r9, r12, rcx; x45, x44<- arg1[5] * x4
mov rdx, [ rsp + 0x78 ]; x7 to rdx
mov [ rsp + 0x120 ], r15; spilling x69 to mem
mulx rdx, r15, [ rsi + 0x30 ]; x43, x42<- arg1[6] * x7
mov [ rsp + 0x128 ], r9; spilling x45 to mem
mov r9, rdx; preserving value of x43 into a new reg
mov rdx, [ rsp + 0xa0 ]; saving x3 in rdx.
mov [ rsp + 0x130 ], r11; spilling x100 to mem
mov [ rsp + 0x138 ], rbx; spilling x92 to mem
mulx r11, rbx, [ rsi + 0x28 ]; x37, x36<- arg1[5] * x3
mov [ rsp + 0x140 ], r9; spilling x43 to mem
mov r9, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x148 ], r11; spilling x37 to mem
mov [ rsp + 0x150 ], r10; spilling x80 to mem
mulx r11, r10, [ rsp + 0x70 ]; x35, x34<- arg1[6] * x6
adox r10, rbx
clc;
adcx r10, r15
setc dl; spill CF x233 to reg (rdx)
clc;
adcx r10, r12
setc r12b; spill CF x237 to reg (r12)
clc;
adcx r10, rbp
seto bpl; spill OF x229 to reg (rbp)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0x150 ]
setc bl; spill CF x241 to reg (rbx)
clc;
adcx r10, [ rsp + 0x138 ]
setc r15b; spill CF x249 to reg (r15)
clc;
adcx r10, [ rsp + 0x130 ]
mov byte [ rsp + 0x158 ], r15b; spilling byte x249 to mem
setc r15b; spill CF x253 to reg (r15)
clc;
adcx r10, [ rsp + 0x118 ]
mov byte [ rsp + 0x160 ], r15b; spilling byte x253 to mem
setc r15b; spill CF x257 to reg (r15)
clc;
adcx r10, [ rsp + 0x110 ]
mov byte [ rsp + 0x168 ], r15b; spilling byte x257 to mem
setc r15b; spill CF x261 to reg (r15)
clc;
adcx r10, [ rsp + 0x108 ]
mov byte [ rsp + 0x170 ], r15b; spilling byte x261 to mem
seto r15b; spill OF x245 to reg (r15)
mov byte [ rsp + 0x178 ], bl; spilling byte x241 to mem
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, [ rsp + 0xf8 ]
movzx rbp, bpl
lea r11, [ rbp + r11 ]
mov rbp, [ rsp + 0x148 ]
lea r11, [rbp+r11]
movzx rdx, dl
lea r11, [ rdx + r11 ]
mov rdx, [ rsp + 0x140 ]
lea r11, [rdx+r11]
movzx r12, r12b
lea r11, [ r12 + r11 ]
mov r12, [ rsp + 0x128 ]
lea r11, [r12+r11]
movzx rbp, byte [ rsp + 0x178 ]; load byte memx241 to register64
lea r11, [ rbp + r11 ]
mov rbp, [ rsp + 0x120 ]
lea r11, [rbp+r11]
movzx r15, r15b
lea r11, [ r15 + r11 ]
mov r15, [ rsp + 0x100 ]
lea r11, [r15+r11]
movzx rdx, byte [ rsp + 0x158 ]; load byte memx249 to register64
lea r11, [ rdx + r11 ]
mov rdx, [ rsp + 0xf0 ]
lea r11, [rdx+r11]
movzx r12, byte [ rsp + 0x160 ]; load byte memx253 to register64
lea r11, [ r12 + r11 ]
mov r12, [ rsp + 0xe8 ]
lea r11, [r12+r11]
movzx rbp, byte [ rsp + 0x168 ]; load byte memx257 to register64
lea r11, [ rbp + r11 ]
mov rbp, [ rsp + 0xe0 ]
lea r11, [rbp+r11]
movzx r15, byte [ rsp + 0x170 ]; load byte memx261 to register64
lea r11, [ r15 + r11 ]
mov r15, [ rsp + 0xd8 ]
lea r11, [r15+r11]
adcx r11, [ rsp + 0xd0 ]
mov rdx, 0x0 ; moving imm to reg
adox r11, rdx
mov r12, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsp + 0x68 ]; saving x5 in rdx.
mulx rdx, rbp, [ rsi + 0x0 ]; x119, x118<- arg1[0] * x5
mov r15, rdx; preserving value of x119 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r12, rbx, [ rsp + 0x60 ]; x107, x106<- arg1[1] * x10
mov rdx, [ rsp + 0x58 ]; x15 to rdx
mov [ rsp + 0x180 ], r13; spilling x20 to mem
mov [ rsp + 0x188 ], rdi; spilling x9 to mem
mulx r13, rdi, [ rsi + 0x10 ]; x95, x94<- arg1[2] * x15
xchg rdx, r8; x18, swapping with x15, which is currently in rdx
mov [ rsp + 0x190 ], r11; spilling x330 to mem
mov [ rsp + 0x198 ], r10; spilling x328 to mem
mulx r11, r10, [ rsi + 0x18 ]; x83, x82<- arg1[3] * x18
xchg rdx, r9; x3, swapping with x18, which is currently in rdx
mov [ rsp + 0x1a0 ], r15; spilling x119 to mem
mov [ rsp + 0x1a8 ], r12; spilling x107 to mem
mulx r15, r12, [ rsi + 0x20 ]; x57, x56<- arg1[4] * x3
mov [ rsp + 0x1b0 ], r13; spilling x95 to mem
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x98 ]; saving x8 in rdx.
mov [ rsp + 0x1b8 ], r11; spilling x83 to mem
mov [ rsp + 0x1c0 ], r15; spilling x57 to mem
mulx r11, r15, [ rsi + 0x28 ]; x49, x48<- arg1[5] * x8
test al, al
adox r15, r12
adcx r15, r10
setc r10b; spill CF x153 to reg (r10)
clc;
adcx r15, rdi
setc dil; spill CF x157 to reg (rdi)
clc;
adcx r15, rbx
setc bl; spill CF x161 to reg (rbx)
clc;
adcx r15, rbp
adox r11, [ rsp + 0x1c0 ]
movzx r10, r10b
lea r11, [ r10 + r11 ]
mov r10, [ rsp + 0x1b8 ]
lea r11, [r10+r11]
movzx rdi, dil
lea r11, [ rdi + r11 ]
mov rdi, [ rsp + 0x1b0 ]
lea r11, [rdi+r11]
movzx rbx, bl
lea r11, [ rbx + r11 ]
mov rbx, [ rsp + 0x1a8 ]
lea r11, [rbx+r11]
adcx r11, [ rsp + 0x1a0 ]
mov rbp, r15; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x331, x332, size: 2
shrd rbp, r11, 56; x331 <- x166||x164 >> 56
mov r12, 0x38 ; moving imm to reg
bzhi r15, r15, r12; x332 <- x164 (only least 0x38 bits)
mov r10, rbp; x333, copying x331 here, cause x331 is needed in a reg for other than x333, namely all: , x333--x334, x338--x339, size: 2
adox r10, [ rsp + 0x198 ]
mov rdi, [ rsp + 0x190 ]; x335, copying x330 here, cause x330 is needed in a reg for other than x335, namely all: , x335, size: 1
mov rbx, 0x0 ; moving imm to reg
adox rdi, rbx
mov r11, r10; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x336, x337, size: 2
shrd r11, rdi, 56; x336 <- x335||x333 >> 56
bzhi r10, r10, r12; x337 <- x333 (only least 0x38 bits)
mov rdi, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r12, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x1c8 ], r10; spilling x337 to mem
mov [ rsp + 0x1d0 ], r15; spilling x332 to mem
mulx r10, r15, rcx; x103, x102<- arg1[1] * x4
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1d8 ], r11; spilling x336 to mem
mov [ rsp + 0x1e0 ], rax; spilling x19 to mem
mulx r11, rax, [ rsp + 0x188 ]; x91, x90<- arg1[2] * x9
mov rdx, [ rsp + 0x48 ]; x14 to rdx
mov [ rsp + 0x1e8 ], rbx; spilling x133 to mem
mov [ rsp + 0x1f0 ], r10; spilling x103 to mem
mulx rbx, r10, [ rsi + 0x18 ]; x79, x78<- arg1[3] * x14
mov [ rsp + 0x1f8 ], r11; spilling x91 to mem
mov r11, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x200 ], rbx; spilling x79 to mem
mov [ rsp + 0x208 ], r12; spilling x132 to mem
mulx rbx, r12, [ rsp + 0x50 ]; x67, x66<- arg1[4] * x17
mov rdx, r13; x3 to rdx
mov [ rsp + 0x210 ], rbx; spilling x67 to mem
mov [ rsp + 0x218 ], r15; spilling x102 to mem
mulx rbx, r15, [ rsi + 0x28 ]; x29, x28<- arg1[5] * x3
mov [ rsp + 0x220 ], rbx; spilling x29 to mem
mov rbx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x70 ]; saving x6 in rdx.
mov [ rsp + 0x228 ], rax; spilling x90 to mem
mulx rdx, rax, [ rsi + 0x30 ]; x27, x26<- arg1[6] * x6
adox rax, r15
clc;
adcx rax, r12
setc r12b; spill CF x309 to reg (r12)
clc;
adcx rax, r10
seto r10b; spill OF x305 to reg (r10)
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, [ rsp + 0x228 ]
seto r15b; spill OF x317 to reg (r15)
mov byte [ rsp + 0x230 ], r12b; spilling byte x309 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, [ rsp + 0x218 ]
setc r12b; spill CF x313 to reg (r12)
clc;
adcx rax, [ rsp + 0x208 ]
mov byte [ rsp + 0x238 ], r15b; spilling byte x317 to mem
seto r15b; spill OF x321 to reg (r15)
mov byte [ rsp + 0x240 ], r12b; spilling byte x313 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rax
movzx r10, r10b
lea rdx, [ r10 + rdx ]
mov r10, [ rsp + 0x220 ]
lea rdx, [r10+rdx]
movzx r10, byte [ rsp + 0x230 ]; load byte memx309 to register64
lea rdx, [ r10 + rdx ]
mov r10, [ rsp + 0x210 ]
lea rdx, [r10+rdx]
movzx r10, byte [ rsp + 0x240 ]; load byte memx313 to register64
lea rdx, [ r10 + rdx ]
mov r10, [ rsp + 0x200 ]
lea rdx, [r10+rdx]
movzx r10, byte [ rsp + 0x238 ]; load byte memx317 to register64
lea rdx, [ r10 + rdx ]
mov r10, [ rsp + 0x1f8 ]
lea rdx, [r10+rdx]
movzx r15, r15b
lea rdx, [ r15 + rdx ]
mov r15, [ rsp + 0x1f0 ]
lea rdx, [r15+rdx]
adcx rdx, [ rsp + 0x1e8 ]
mov r10, 0x0 ; moving imm to reg
adox rdx, r10
xchg rdx, r8; x15, swapping with x340, which is currently in rdx
mulx r15, rax, [ rsi + 0x0 ]; x123, x122<- arg1[0] * x15
mov r10, rdx; preserving value of x15 into a new reg
mov rdx, [ rsp + 0x1e0 ]; saving x19 in rdx.
mulx rdx, r12, [ rsi + 0x10 ]; x99, x98<- arg1[2] * x19
mov [ rsp + 0x248 ], r8; spilling x340 to mem
mov r8, rdx; preserving value of x99 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x250 ], rbp; spilling x338 to mem
mov [ rsp + 0x258 ], r15; spilling x123 to mem
mulx rbp, r15, r9; x111, x110<- arg1[1] * x18
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x260 ], rbp; spilling x111 to mem
mov [ rsp + 0x268 ], r8; spilling x99 to mem
mulx rbp, r8, rbx; x89, x88<- arg1[2] * x3
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x270 ], rbp; spilling x89 to mem
mov [ rsp + 0x278 ], rax; spilling x122 to mem
mulx rbp, rax, rdi; x77, x76<- arg1[3] * x8
mov rdx, [ rsp + 0x90 ]; x13 to rdx
mov [ rsp + 0x280 ], rbp; spilling x77 to mem
mulx rdx, rbp, [ rsi + 0x20 ]; x65, x64<- arg1[4] * x13
xchg rdx, rcx; x4, swapping with x65, which is currently in rdx
mov [ rsp + 0x288 ], rcx; spilling x65 to mem
mov [ rsp + 0x290 ], r15; spilling x110 to mem
mulx rcx, r15, [ rsi + 0x30 ]; x41, x40<- arg1[6] * x4
xchg rdx, rbx; x3, swapping with x4, which is currently in rdx
mov [ rsp + 0x298 ], rcx; spilling x41 to mem
mov [ rsp + 0x2a0 ], r12; spilling x98 to mem
mulx rcx, r12, [ rsi + 0x30 ]; x33, x32<- arg1[6] * x3
add r12, r15; could be done better, if r0 has been u8 as well
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rbp
seto bpl; spill OF x205 to reg (rbp)
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, rax
setc al; spill CF x201 to reg (rax)
clc;
adcx r12, r8
seto r8b; spill OF x209 to reg (r8)
mov byte [ rsp + 0x2a8 ], bpl; spilling byte x205 to mem
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, [ rsp + 0x2a0 ]
setc bpl; spill CF x213 to reg (rbp)
clc;
adcx r12, [ rsp + 0x290 ]
mov byte [ rsp + 0x2b0 ], bpl; spilling byte x213 to mem
setc bpl; spill CF x221 to reg (rbp)
clc;
adcx r12, [ rsp + 0x278 ]
mov byte [ rsp + 0x2b8 ], bpl; spilling byte x221 to mem
setc bpl; spill CF x225 to reg (rbp)
clc;
adcx r12, [ rsp + 0x1d8 ]
movzx rax, al
lea rcx, [ rax + rcx ]
mov rax, [ rsp + 0x298 ]
lea rcx, [rax+rcx]
movzx rax, byte [ rsp + 0x2a8 ]; load byte memx205 to register64
lea rcx, [ rax + rcx ]
mov rax, [ rsp + 0x288 ]
lea rcx, [rax+rcx]
movzx r8, r8b
lea rcx, [ r8 + rcx ]
mov r8, [ rsp + 0x280 ]
lea rcx, [r8+rcx]
movzx rax, byte [ rsp + 0x2b0 ]; load byte memx213 to register64
lea rcx, [ rax + rcx ]
mov rax, [ rsp + 0x270 ]
lea rcx, [rax+rcx]
adox rcx, [ rsp + 0x268 ]
movzx r8, byte [ rsp + 0x2b8 ]; load byte memx221 to register64
lea rcx, [ r8 + rcx ]
mov r8, [ rsp + 0x260 ]
lea rcx, [r8+rcx]
movzx rbp, bpl
lea rcx, [ rbp + rcx ]
mov rbp, [ rsp + 0x258 ]
lea rcx, [rbp+rcx]
adc rcx, 0x0
mov rax, [ rsp + 0x250 ]; load m64 x338 to register64
mov r8, [ rsp + 0x248 ]; load m64 x340 to register64
mov rbp, rax; x344, copying x338 here, cause x338 is needed in a reg for other than x344, namely all: , x344, x345, size: 2
shrd rbp, r8, 56; x344 <- x340||x338 >> 56
mov r8, 0xffffffffffffff ; moving imm to reg
and rax, r8; x345 <- x338&0xffffffffffffff
mov r15, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x88 ]; saving x21 in rdx.
mulx rdx, r8, [ rsi + 0x0 ]; x131, x130<- arg1[0] * x21
mov [ rsp + 0x2c0 ], rax; spilling x345 to mem
mov rax, rdx; preserving value of x131 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x2c8 ], rcx; spilling x343 to mem
mov [ rsp + 0x2d0 ], r12; spilling x341 to mem
mulx rcx, r12, rbx; x87, x86<- arg1[2] * x4
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x2d8 ], rax; spilling x131 to mem
mov [ rsp + 0x2e0 ], rcx; spilling x87 to mem
mulx rax, rcx, [ rsp + 0x188 ]; x75, x74<- arg1[3] * x9
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x2e8 ], rax; spilling x75 to mem
mulx r11, rax, r11; x63, x62<- arg1[4] * x14
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x2f0 ], r11; spilling x63 to mem
mov [ rsp + 0x2f8 ], rbp; spilling x344 to mem
mulx r11, rbp, r15; x25, x24<- arg1[6] * x3
adox rbp, rax
adcx rbp, rcx
setc dl; spill CF x293 to reg (rdx)
clc;
adcx rbp, r12
setc r12b; spill CF x297 to reg (r12)
clc;
adcx rbp, r8
setc r8b; spill CF x301 to reg (r8)
clc;
adcx rbp, [ rsp + 0x2f8 ]
adox r11, [ rsp + 0x2f0 ]
movzx rdx, dl
lea r11, [ rdx + r11 ]
mov rdx, [ rsp + 0x2e8 ]
lea r11, [rdx+r11]
movzx r12, r12b
lea r11, [ r12 + r11 ]
mov r12, [ rsp + 0x2e0 ]
lea r11, [r12+r11]
movzx r8, r8b
lea r11, [ r8 + r11 ]
mov r8, [ rsp + 0x2d8 ]
lea r11, [r8+r11]
adc r11, 0x0
mov rcx, [ rsp + 0x2d0 ]; load m64 x341 to register64
mov rax, [ rsp + 0x2c8 ]; load m64 x343 to register64
mov rdx, rcx; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x349, x350, size: 2
shrd rdx, rax, 56; x349 <- x343||x341 >> 56
mov rax, 0x38 ; moving imm to reg
bzhi rcx, rcx, rax; x350 <- x341 (only least 0x38 bits)
mov r12, rdx; preserving value of x349 into a new reg
mov rdx, [ rsp + 0x60 ]; saving x10 in rdx.
mulx rdx, r8, [ rsi + 0x0 ]; x121, x120<- arg1[0] * x10
mov rax, rdx; preserving value of x121 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x300 ], rcx; spilling x350 to mem
mulx r10, rcx, r10; x109, x108<- arg1[1] * x15
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x308 ], r11; spilling x348 to mem
mulx r9, r11, r9; x97, x96<- arg1[2] * x18
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x310 ], rbp; spilling x346 to mem
mov [ rsp + 0x318 ], rax; spilling x121 to mem
mulx rbp, rax, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x320 ], r10; spilling x109 to mem
mulx r15, r10, r15; x73, x72<- arg1[3] * x3
mov rdx, rdi; x8 to rdx
mov [ rsp + 0x328 ], r9; spilling x97 to mem
mulx rdx, r9, [ rsi + 0x20 ]; x61, x60<- arg1[4] * x8
mov [ rsp + 0x330 ], rbp; spilling x85 to mem
mov rbp, rdx; preserving value of x61 into a new reg
mov rdx, [ rsp + 0xc8 ]; saving x11 in rdx.
mov [ rsp + 0x338 ], r15; spilling x73 to mem
mulx rdx, r15, [ rsi + 0x28 ]; x53, x52<- arg1[5] * x11
mov [ rsp + 0x340 ], rbp; spilling x61 to mem
mov rbp, rdx; preserving value of x53 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x348 ], r12; spilling x349 to mem
mov [ rsp + 0x350 ], r8; spilling x120 to mem
mulx r12, r8, [ rsp + 0x40 ]; x39, x38<- arg1[7] * x2
mov rdx, [ rsp + 0x38 ]; x1 to rdx
mov [ rsp + 0x358 ], rbp; spilling x53 to mem
mov [ rsp + 0x360 ], r12; spilling x39 to mem
mulx rbp, r12, [ rsi + 0x38 ]; x31, x30<- arg1[7] * x1
adox r12, r8
clc;
adcx r12, r15
seto r15b; spill OF x169 to reg (r15)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r9
seto r9b; spill OF x177 to reg (r9)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r10
seto r10b; spill OF x181 to reg (r10)
mov byte [ rsp + 0x368 ], r9b; spilling byte x177 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, rax
setc al; spill CF x173 to reg (rax)
clc;
adcx r12, r11
setc r11b; spill CF x189 to reg (r11)
clc;
adcx r12, rcx
setc cl; spill CF x193 to reg (rcx)
clc;
adcx r12, [ rsp + 0x350 ]
seto r9b; spill OF x185 to reg (r9)
mov byte [ rsp + 0x370 ], cl; spilling byte x193 to mem
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, [ rsp + 0x348 ]
movzx r15, r15b
lea rbp, [ r15 + rbp ]
mov r15, [ rsp + 0x360 ]
lea rbp, [r15+rbp]
movzx rax, al
lea rbp, [ rax + rbp ]
mov rax, [ rsp + 0x358 ]
lea rbp, [rax+rbp]
movzx r15, byte [ rsp + 0x368 ]; load byte memx177 to register64
lea rbp, [ r15 + rbp ]
mov r15, [ rsp + 0x340 ]
lea rbp, [r15+rbp]
movzx r10, r10b
lea rbp, [ r10 + rbp ]
mov r10, [ rsp + 0x338 ]
lea rbp, [r10+rbp]
movzx r9, r9b
lea rbp, [ r9 + rbp ]
mov r9, [ rsp + 0x330 ]
lea rbp, [r9+rbp]
movzx r11, r11b
lea rbp, [ r11 + rbp ]
mov r11, [ rsp + 0x328 ]
lea rbp, [r11+rbp]
movzx rax, byte [ rsp + 0x370 ]; load byte memx193 to register64
lea rbp, [ rax + rbp ]
mov rax, [ rsp + 0x320 ]
lea rbp, [rax+rbp]
adcx rbp, [ rsp + 0x318 ]
adox rbp, r8
mov r15, [ rsp + 0x310 ]; load m64 x346 to register64
mov r10, [ rsp + 0x308 ]; load m64 x348 to register64
mov r9, r15; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x354, x355, size: 2
shrd r9, r10, 56; x354 <- x348||x346 >> 56
mov r10, 0xffffffffffffff ; moving imm to reg
and r15, r10; x355 <- x346&0xffffffffffffff
mov r11, rdx; preserving value of x1 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rax, r8, [ rsp + 0x180 ]; x129, x128<- arg1[0] * x20
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r10, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
mov rdx, rbx; x4 to rdx
mov [ rsp + 0x378 ], r15; spilling x355 to mem
mulx rdx, r15, [ rsi + 0x18 ]; x71, x70<- arg1[3] * x4
mov [ rsp + 0x380 ], rbp; spilling x353 to mem
mov rbp, rdx; preserving value of x71 into a new reg
mov rdx, [ rsp + 0x188 ]; saving x9 in rdx.
mov [ rsp + 0x388 ], r12; spilling x351 to mem
mulx rdx, r12, [ rsi + 0x20 ]; x59, x58<- arg1[4] * x9
mov [ rsp + 0x390 ], rax; spilling x129 to mem
mov rax, rdx; preserving value of x59 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x398 ], rcx; spilling x117 to mem
mov [ rsp + 0x3a0 ], rbp; spilling x71 to mem
mulx rcx, rbp, [ rsp + 0xc0 ]; x51, x50<- arg1[5] * x12
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x3a8 ], rax; spilling x59 to mem
mulx r11, rax, r11; x23, x22<- arg1[7] * x1
adox rax, rbp
adcx rax, r12
seto dl; spill OF x269 to reg (rdx)
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r15
seto r15b; spill OF x277 to reg (r15)
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, r10
setc r10b; spill CF x273 to reg (r10)
clc;
adcx rax, r8
setc r8b; spill CF x285 to reg (r8)
clc;
adcx rax, r9
movzx rdx, dl
lea rcx, [ rcx + r11 ]
lea rcx, [ rcx + rdx ]
movzx r10, r10b
lea rcx, [ r10 + rcx ]
mov r10, [ rsp + 0x3a8 ]
lea rcx, [r10+rcx]
movzx r15, r15b
lea rcx, [ r15 + rcx ]
mov r15, [ rsp + 0x3a0 ]
lea rcx, [r15+rcx]
adox rcx, [ rsp + 0x398 ]
movzx r8, r8b
lea rcx, [ r8 + rcx ]
mov r8, [ rsp + 0x390 ]
lea rcx, [r8+rcx]
adc rcx, 0x0
mov r9, [ rsp + 0x388 ]; load m64 x351 to register64
mov rbp, [ rsp + 0x380 ]; load m64 x353 to register64
mov r11, r9; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x359, x360, size: 2
shrd r11, rbp, 56; x359 <- x353||x351 >> 56
mov rbp, 0x38 ; moving imm to reg
bzhi r9, r9, rbp; x360 <- x351 (only least 0x38 bits)
add r11, [ rsp + 0x1d0 ]
mov rdx, rax; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x362, x363, size: 2
shrd rdx, rcx, 56; x362 <- x358||x356 >> 56
mov r10, 0xffffffffffffff ; moving imm to reg
and rax, r10; x363 <- x356&0xffffffffffffff
add rdx, [ rsp + 0xb8 ]
mov r15, r11; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, x366, size: 2
shr r15, 56; x365 <- x361>> 56
and r11, r10; x366 <- x361&0xffffffffffffff
mov r8, rdx; x367, copying x364 here, cause x364 is needed in a reg for other than x367, namely all: , x367, x368, size: 2
shr r8, 56; x367 <- x364>> 56
bzhi rdx, rdx, rbp; x368 <- x364 (only least 0x38 bits)
mov rcx, r15; x369, copying x365 here, cause x365 is needed in a reg for other than x369, namely all: , x369, x370, size: 2
add rcx, [ rsp + 0x1c8 ]
add r15, [ rsp + 0x2c0 ]
lea r8, [ r8 + rcx ]
mov rcx, r8; x372, copying x371 here, cause x371 is needed in a reg for other than x372, namely all: , x372, x373, size: 2
shr rcx, 56; x372 <- x371>> 56
and r8, r10; x373 <- x371&0xffffffffffffff
add rcx, [ rsp + 0x300 ]
mov r12, r15; x375, copying x370 here, cause x370 is needed in a reg for other than x375, namely all: , x375, x376, size: 2
shr r12, 56; x375 <- x370>> 56
bzhi r15, r15, rbp; x376 <- x370 (only least 0x38 bits)
add r12, [ rsp + 0x378 ]
mov rbp, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ rbp + 0x0 ], r15; out1[0] = x376
mov [ rbp + 0x8 ], r12; out1[1] = x377
mov [ rbp + 0x10 ], rax; out1[2] = x363
mov [ rbp + 0x18 ], rdx; out1[3] = x368
mov [ rbp + 0x20 ], r8; out1[4] = x373
mov [ rbp + 0x28 ], rcx; out1[5] = x374
mov [ rbp + 0x30 ], r9; out1[6] = x360
mov [ rbp + 0x38 ], r11; out1[7] = x366
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x3b0 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.5675
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2784 ms / 10 evals=> 278.4ms/eval
; Time spent for assembling and measureing (initial batch_size=71, initial num_batches=31): 66 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.023706896551724137
; number reverted permutation/ tried permutation: 5 / 6 =83.333%
; number reverted decision/ tried decision: 0 / 4 =0.000%