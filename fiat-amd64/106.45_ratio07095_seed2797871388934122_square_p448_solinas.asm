SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x270 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x240 ], rbx; saving to stack
mov [ rsp + 0x248 ], rbp; saving to stack
mov [ rsp + 0x250 ], r12; saving to stack
mov [ rsp + 0x258 ], r13; saving to stack
mov [ rsp + 0x260 ], r14; saving to stack
mov [ rsp + 0x268 ], r15; saving to stack
imul rax, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
mov r10, [ rsi + 0x30 ]; load m64 x7 to register64
imul r11, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov rbx, [ rsi + 0x38 ]; load m64 x2 to register64
mov rdx, r11; x20 to rdx
mulx r11, rbp, [ rsi + 0x8 ]; x115, x114<- arg1[1] * x20
imul r12, rbx, 0x2; x4 <- x2 * 0x2
mov r13, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r15, rax; x127, x126<- arg1[0] * x19
imul rdx, r10, 0x2; x9 <- x7 * 0x2
mov rcx, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r8, r9, r12; x55, x54<- arg1[4] * x4
mov rdx, rcx; x9 to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rcx, rdi, [ rsi + 0x28 ]; x47, x46<- arg1[5] * x9
test al, al
adox rdi, r9
adox r8, rcx
adcx rdi, rbp
setc bpl; spill CF x139 to reg (rbp)
imul r9, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
mov rcx, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x8 ], r13; spilling x20 to mem
mov [ rsp + 0x10 ], rbx; spilling x2 to mem
mulx r13, rbx, rax; x113, x112<- arg1[1] * x19
sar  bpl, 1
adcx r11, r8
mov rdx, r12; x4 to rdx
mulx r12, r8, [ rsi + 0x28 ]; x45, x44<- arg1[5] * x4
mov rbp, [ rsi + 0x28 ]; load m64 x11 to register64
adox rdi, r15
adox r14, r11
mov r15, rdi; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd r15, r14, 56; x146 <- x144||x142 >> 56
mov r11, [ rsi + 0x38 ]; load m64 x1 to register64
imul r14, r11, 0x2; x3 <- x1 * 0x2
mov [ rsp + 0x18 ], r13; spilling x113 to mem
mov r13, [ rsi + 0x30 ]; load m64 x6 to register64
mov [ rsp + 0x20 ], r12; spilling x45 to mem
mov r12, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x28 ], r15; spilling x146 to mem
mulx r10, r15, r10; x43, x42<- arg1[6] * x7
mov rdx, r14; x3 to rdx
mov [ rsp + 0x30 ], r10; spilling x43 to mem
mulx r14, r10, [ rsi + 0x28 ]; x37, x36<- arg1[5] * x3
mov [ rsp + 0x38 ], rcx; spilling x9 to mem
imul rcx, r13, 0x2; x8 <- x6 * 0x2
mov [ rsp + 0x40 ], r14; spilling x37 to mem
imul r14, rbp, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x48 ], rbx; spilling x112 to mem
mov rbx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x50 ], r8; spilling x44 to mem
mov [ rsp + 0x58 ], r15; spilling x42 to mem
mulx r8, r15, rcx; x93, x92<- arg1[2] * x8
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x60 ], r8; spilling x93 to mem
mov [ rsp + 0x68 ], r15; spilling x92 to mem
mulx r8, r15, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x70 ], r8; spilling x101 to mem
mov [ rsp + 0x78 ], r15; spilling x100 to mem
mulx r8, r15, r9; x125, x124<- arg1[0] * x18
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x80 ], r8; spilling x125 to mem
mov [ rsp + 0x88 ], r15; spilling x124 to mem
mulx r8, r15, r14; x81, x80<- arg1[3] * x13
mov rdx, r13; x6 to rdx
mov [ rsp + 0x90 ], r8; spilling x81 to mem
mulx r13, r8, [ rsi + 0x30 ]; x35, x34<- arg1[6] * x6
xchg rdx, rbx; x3, swapping with x6, which is currently in rdx
mov [ rsp + 0x98 ], r13; spilling x35 to mem
mov [ rsp + 0xa0 ], r15; spilling x80 to mem
mulx r13, r15, [ rsi + 0x8 ]; x105, x104<- arg1[1] * x3
mov [ rsp + 0xa8 ], r13; spilling x105 to mem
mov r13, [ rsi + 0x20 ]; load m64 x16 to register64
xchg rdx, r13; x16, swapping with x3, which is currently in rdx
mov [ rsp + 0xb0 ], r15; spilling x104 to mem
mulx rdx, r15, [ rsi + 0x20 ]; x69, x68<- arg1[4] * x16
mov [ rsp + 0xb8 ], rdx; spilling x69 to mem
xor rdx, rdx
adox r8, r10
adcx r8, [ rsp + 0x58 ]
setc r10b; spill CF x233 to reg (r10)
clc;
adcx r8, [ rsp + 0x50 ]
mov byte [ rsp + 0xc0 ], r10b; spilling byte x233 to mem
seto r10b; spill OF x229 to reg (r10)
mov [ rsp + 0xc8 ], r14; spilling x13 to mem
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r15
setc r15b; spill CF x237 to reg (r15)
clc;
adcx r8, [ rsp + 0xa0 ]
setc r14b; spill CF x245 to reg (r14)
clc;
adcx r8, [ rsp + 0x68 ]
mov [ rsp + 0xd0 ], rax; spilling x19 to mem
mov rax, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0xd8 ], r14b; spilling byte x245 to mem
mov byte [ rsp + 0xe0 ], r15b; spilling byte x237 to mem
mulx r14, r15, r13; x57, x56<- arg1[4] * x3
setc dl; spill CF x249 to reg (rdx)
clc;
adcx r8, [ rsp + 0x78 ]
mov byte [ rsp + 0xe8 ], dl; spilling byte x249 to mem
setc dl; spill CF x253 to reg (rdx)
clc;
adcx r8, [ rsp + 0xb0 ]
mov byte [ rsp + 0xf0 ], dl; spilling byte x253 to mem
setc dl; spill CF x257 to reg (rdx)
clc;
adcx r8, [ rsp + 0x48 ]
setc al; spill CF x261 to reg (rax)
mov byte [ rsp + 0xf8 ], dl; spilling byte x257 to mem
seto dl; spill OF x241 to reg (rdx)
mov byte [ rsp + 0x100 ], r10b; spilling byte x229 to mem
imul r10, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov [ rsp + 0x108 ], r12; spilling x4 to mem
mov r12b, dl; preserving value of x241 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov byte [ rsp + 0x110 ], al; spilling byte x261 to mem
mulx r10, rax, r10; x119, x118<- arg1[0] * x5
imul rdx, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
test al, al
adox r8, [ rsp + 0x88 ]
xchg rdx, rcx; x8, swapping with x10, which is currently in rdx
mov [ rsp + 0x118 ], r10; spilling x119 to mem
mov [ rsp + 0x120 ], rax; spilling x118 to mem
mulx r10, rax, [ rsi + 0x28 ]; x49, x48<- arg1[5] * x8
mov byte [ rsp + 0x128 ], r12b; spilling byte x241 to mem
seto r12b; spill OF x265 to reg (r12)
mov [ rsp + 0x130 ], rcx; spilling x10 to mem
imul rcx, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov byte [ rsp + 0x138 ], r12b; spilling byte x265 to mem
xor r12, r12
adox r8, [ rsp + 0x28 ]
xchg rdx, rcx; x15, swapping with x8, which is currently in rdx
mov [ rsp + 0x140 ], r8; spilling x328 to mem
mulx r12, r8, [ rsi + 0x10 ]; x95, x94<- arg1[2] * x15
adcx rax, r15
adcx r14, r10
mov r15, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x148 ], rdi; spilling x142 to mem
mulx r10, rdi, [ rsp + 0x130 ]; x107, x106<- arg1[1] * x10
mov rdx, r9; x18 to rdx
mov [ rsp + 0x150 ], r10; spilling x107 to mem
mulx r9, r10, [ rsi + 0x18 ]; x83, x82<- arg1[3] * x18
clc;
adcx rax, r10
adcx r9, r14
mov r14, [ rsp + 0x40 ]; load m64 x37 to register64
movzx r10, byte [ rsp + 0x100 ]; load byte memx229 to register64
lea r14, [ r10 + r14 ]
mov r10, [ rsp + 0x98 ]
lea r14, [r10+r14]
movzx r10, byte [ rsp + 0xc0 ]; load byte memx233 to register64
lea r14, [ r10 + r14 ]
mov r10, [ rsp + 0x30 ]
lea r14, [r10+r14]
clc;
adcx rax, r8
seto r10b; spill OF x329 to reg (r10)
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, rdi
movzx rdi, byte [ rsp + 0xe0 ]; load byte memx237 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x20 ]
lea r14, [rdi+r14]
adcx r12, r9
movzx rdi, byte [ rsp + 0x128 ]; load byte memx241 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0xb8 ]
lea r14, [rdi+r14]
movzx rdi, byte [ rsp + 0xd8 ]; load byte memx245 to register64
lea r14, [ rdi + r14 ]
mov rdi, [ rsp + 0x90 ]
lea r14, [rdi+r14]
clc;
adcx rax, [ rsp + 0x120 ]
xchg rdx, r15; x15, swapping with x18, which is currently in rdx
mulx rdi, r9, [ rsi + 0x0 ]; x123, x122<- arg1[0] * x15
adox r12, [ rsp + 0x150 ]
adcx r12, [ rsp + 0x118 ]
sar byte [ rsp + 0xe8 ], 1
adcx r14, [ rsp + 0x60 ]
sar byte [ rsp + 0xf0 ], 1
adcx r14, [ rsp + 0x70 ]
sar byte [ rsp + 0xf8 ], 1
adcx r14, [ rsp + 0xa8 ]
mov r8, rdx; preserving value of x15 into a new reg
mov rdx, [ rsp + 0xd0 ]; saving x19 in rdx.
mov [ rsp + 0x158 ], rbp; spilling x11 to mem
mulx rdx, rbp, [ rsi + 0x10 ]; x99, x98<- arg1[2] * x19
sar byte [ rsp + 0x110 ], 1
adcx r14, [ rsp + 0x18 ]
sar byte [ rsp + 0x138 ], 1
adcx r14, [ rsp + 0x80 ]
mov [ rsp + 0x160 ], rdi; spilling x123 to mem
mov rdi, rax; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x331, x332, size: 2
shrd rdi, r12, 56; x331 <- x166||x164 >> 56
movzx r12, r10b; x330, copying x329 here, cause x329 is needed in a reg for other than x330, namely all: , x330, size: 1
lea r12, [ r12 + r14 ]
mov r10, rdx; preserving value of x99 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x168 ], r9; spilling x122 to mem
mulx r14, r9, [ rsp + 0x108 ]; x41, x40<- arg1[6] * x4
mov rdx, rdi; x333, copying x331 here, cause x331 is needed in a reg for other than x333, namely all: , x333--x334, x338--x339, size: 2
add rdx, [ rsp + 0x140 ]; could be done better, if r0 has been u8 as well
adc r12, 0x0
mov [ rsp + 0x170 ], r10; spilling x99 to mem
mov r10, rdx; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x336, x337, size: 2
shrd r10, r12, 56; x336 <- x335||x333 >> 56
mov r12, rdx; preserving value of x333 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x178 ], r10; spilling x336 to mem
mov [ rsp + 0x180 ], rbp; spilling x98 to mem
mulx r10, rbp, rcx; x77, x76<- arg1[3] * x8
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x188 ], r10; spilling x77 to mem
mov [ rsp + 0x190 ], r11; spilling x1 to mem
mulx r10, r11, r13; x89, x88<- arg1[2] * x3
mov rdx, r15; x18 to rdx
mov [ rsp + 0x198 ], r10; spilling x89 to mem
mulx r15, r10, [ rsi + 0x8 ]; x111, x110<- arg1[1] * x18
xchg rdx, r13; x3, swapping with x18, which is currently in rdx
mov [ rsp + 0x1a0 ], r15; spilling x111 to mem
mov [ rsp + 0x1a8 ], r10; spilling x110 to mem
mulx r15, r10, [ rsi + 0x30 ]; x33, x32<- arg1[6] * x3
test al, al
adox r10, r9
adox r14, r15
mov r9, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, r15, r8; x109, x108<- arg1[1] * x15
mov rdx, [ rsp + 0xc8 ]; x13 to rdx
mov [ rsp + 0x1b0 ], rbx; spilling x6 to mem
mulx rdx, rbx, [ rsi + 0x20 ]; x65, x64<- arg1[4] * x13
adcx r10, rbx
adcx rdx, r14
add r10, rbp; could be done better, if r0 has been u8 as well
mov rbp, rdx; preserving value of x206 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx r14, rbx, [ rsp + 0x190 ]; x31, x30<- arg1[7] * x1
adcx rbp, [ rsp + 0x188 ]
xor rdx, rdx
adox r10, r11
adox rbp, [ rsp + 0x198 ]
adcx r10, [ rsp + 0x180 ]
adcx rbp, [ rsp + 0x170 ]
xor r11, r11
adox r10, [ rsp + 0x1a8 ]
mov rdx, r9; x3 to rdx
mulx r9, r11, [ rsi + 0x18 ]; x73, x72<- arg1[3] * x3
adcx r10, [ rsp + 0x168 ]
adox rbp, [ rsp + 0x1a0 ]
mov [ rsp + 0x1b8 ], r8; spilling x109 to mem
mov r8, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x1c0 ], r15; spilling x108 to mem
mulx r13, r15, r13; x97, x96<- arg1[2] * x18
adcx rbp, [ rsp + 0x160 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x1c8 ], r13; spilling x97 to mem
mov [ rsp + 0x1d0 ], r15; spilling x96 to mem
mulx r13, r15, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
xor rdx, rdx
adox r10, [ rsp + 0x178 ]
adox rbp, rdx
mov [ rsp + 0x1d8 ], r13; spilling x85 to mem
mov r13, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x1e0 ], r9; spilling x73 to mem
mov [ rsp + 0x1e8 ], r15; spilling x84 to mem
mulx r9, r15, [ rsp + 0x130 ]; x121, x120<- arg1[0] * x10
mov rdx, [ rsp + 0x10 ]; x2 to rdx
mulx rdx, r13, [ rsi + 0x38 ]; x39, x38<- arg1[7] * x2
adcx rbx, r13
setc r13b; spill CF x169 to reg (r13)
mov [ rsp + 0x1f0 ], r9; spilling x121 to mem
mov r9, r10; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd r9, rbp, 56; x349 <- x343||x341 >> 56
sar  r13b, 1
adcx rdx, r14
mov r14, rdx; preserving value of x170 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rbp, r13, [ rsp + 0x158 ]; x53, x52<- arg1[5] * x11
adox rbx, r13
adox rbp, r14
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rcx, r14, rcx; x61, x60<- arg1[4] * x8
test al, al
adox rbx, r14
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, r14, [ rsp + 0x38 ]; x91, x90<- arg1[2] * x9
adox rcx, rbp
adcx rbx, r11
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x1e8 ]
adcx rcx, [ rsp + 0x1e0 ]
adox rcx, [ rsp + 0x1d8 ]
xor r11, r11
adox rbx, [ rsp + 0x1d0 ]
adcx rbx, [ rsp + 0x1c0 ]
adox rcx, [ rsp + 0x1c8 ]
adcx rcx, [ rsp + 0x1b8 ]
test al, al
adox rbx, r15
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r15, rbp, r8; x29, x28<- arg1[5] * x3
adox rcx, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x28 ]; load m64 x12 to register64
adcx rbx, r9
adc rcx, 0x0
mov r9, rbx; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x360, x359, size: 2
shrd r9, rcx, 56; x359 <- x353||x351 >> 56
mov rcx, 0xffffffffffffff ; moving imm to reg
and rax, rcx; x332 <- x164&0xffffffffffffff
imul r11, rdx, 0x2; x14 <- x12 * 0x2
mov rcx, [ rsi + 0x20 ]; load m64 x17 to register64
lea r9, [ r9 + rax ]
mov rax, r9; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, x366, size: 2
shr rax, 56; x365 <- x361>> 56
mov [ rsp + 0x1f8 ], rax; spilling x365 to mem
mov rax, rdx; preserving value of x12 into a new reg
mov rdx, [ rsp + 0x1b0 ]; saving x6 in rdx.
mov [ rsp + 0x200 ], r13; spilling x91 to mem
mulx rdx, r13, [ rsi + 0x30 ]; x27, x26<- arg1[6] * x6
mov [ rsp + 0x208 ], r14; spilling x90 to mem
mov r14, 0xffffffffffffff ; moving imm to reg
and r10, r14; x350 <- x341&0xffffffffffffff
mov r14, rdx; preserving value of x27 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x210 ], r10; spilling x350 to mem
mov [ rsp + 0x218 ], rcx; spilling x17 to mem
mulx r10, rcx, [ rsp + 0x108 ]; x103, x102<- arg1[1] * x4
mov rdx, r11; x14 to rdx
mov [ rsp + 0x220 ], r10; spilling x103 to mem
mulx r11, r10, [ rsi + 0x18 ]; x79, x78<- arg1[3] * x14
adox r13, rbp
adox r15, r14
mov rbp, rdx; preserving value of x14 into a new reg
mov rdx, [ rsp + 0x218 ]; saving x17 in rdx.
mulx rdx, r14, [ rsi + 0x20 ]; x67, x66<- arg1[4] * x17
adcx r13, r14
adcx rdx, r15
xchg rdx, r8; x3, swapping with x310, which is currently in rdx
mulx rdx, r15, [ rsi + 0x30 ]; x25, x24<- arg1[6] * x3
test al, al
adox r13, r10
adox r11, r8
mov r10, rdx; preserving value of x25 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r14, r8, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
adcx r13, [ rsp + 0x208 ]
adcx r11, [ rsp + 0x200 ]
imul rdx, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
add r13, rcx; could be done better, if r0 has been u8 as well
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r8
adcx r11, [ rsp + 0x220 ]
mov r8, rdx; preserving value of x21 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbp, rcx, rbp; x63, x62<- arg1[4] * x14
clc;
adcx rdi, r13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x228 ], r10; spilling x25 to mem
mulx r13, r10, [ rsp + 0x38 ]; x75, x74<- arg1[3] * x9
adox r14, r11
adc r14, 0x0
mov rdx, rdi; x344, copying x338 here, cause x338 is needed in a reg for other than x344, namely all: , x344, x345, size: 2
shrd rdx, r14, 56; x344 <- x340||x338 >> 56
xchg rdx, r8; x21, swapping with x344, which is currently in rdx
mulx rdx, r11, [ rsi + 0x0 ]; x131, x130<- arg1[0] * x21
add r15, rcx; could be done better, if r0 has been u8 as well
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r10
adcx rbp, [ rsp + 0x228 ]
mov r10, rdx; preserving value of x131 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r14, rcx, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x230 ], r14; spilling x117 to mem
mov [ rsp + 0x238 ], rcx; spilling x116 to mem
mulx r14, rcx, [ rsp + 0x108 ]; x87, x86<- arg1[2] * x4
clc;
adcx r15, rcx
adox r13, rbp
adcx r14, r13
test al, al
adox r15, r11
mov rdx, [ rsp + 0x190 ]; x1 to rdx
mulx rdx, r11, [ rsi + 0x38 ]; x23, x22<- arg1[7] * x1
mov rbp, rdx; preserving value of x23 into a new reg
mov rdx, [ rsp + 0x38 ]; saving x9 in rdx.
mulx rdx, rcx, [ rsi + 0x20 ]; x59, x58<- arg1[4] * x9
adcx r15, r8
mov r8, rdx; preserving value of x59 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rax, r13, rax; x51, x50<- arg1[5] * x12
adox r10, r14
adc r10, 0x0
test al, al
adox r11, r13
adcx r11, rcx
adox rax, rbp
mov rdx, [ rsp + 0x108 ]; x4 to rdx
mulx rdx, r14, [ rsi + 0x18 ]; x71, x70<- arg1[3] * x4
adcx r8, rax
add r11, r14; could be done better, if r0 has been u8 as well
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x238 ]
adcx rdx, r8
adox rdx, [ rsp + 0x230 ]
mov rcx, rdx; preserving value of x282 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, rax, [ rsp + 0x8 ]; x129, x128<- arg1[0] * x20
mov rdx, 0xffffffffffffff ; moving imm to reg
and r12, rdx; x337 <- x333&0xffffffffffffff
mov r14, r15; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x355, x354, size: 2
shrd r14, r10, 56; x354 <- x348||x346 >> 56
add r11, rax; could be done better, if r0 has been u8 as well
adcx r13, rcx
xor r10, r10
adox r11, r14
adox r13, r10
mov r8, r11; x363, copying x356 here, cause x356 is needed in a reg for other than x363, namely all: , x363, x362, size: 2
and r8, rdx; x363 <- x356&0xffffffffffffff
mov rcx, [ rsp + 0x148 ]; x147, copying x142 here, cause x142 is needed in a reg for other than x147, namely all: , x147, size: 1
and rcx, rdx; x147 <- x142&0xffffffffffffff
shrd r11, r13, 56; x362 <- x358||x356 >> 56
lea r11, [ r11 + rcx ]
add r12, [ rsp + 0x1f8 ]
and rbx, rdx; x360 <- x351&0xffffffffffffff
mov rax, r11; x367, copying x364 here, cause x364 is needed in a reg for other than x367, namely all: , x367, x368, size: 2
shr rax, 56; x367 <- x364>> 56
and rdi, rdx; x345 <- x338&0xffffffffffffff
and r15, rdx; x355 <- x346&0xffffffffffffff
add rdi, [ rsp + 0x1f8 ]
lea rax, [ rax + r12 ]
and r11, rdx; x368 <- x364&0xffffffffffffff
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x10 ], r8; out1[2] = x363
mov r13, rax; x372, copying x371 here, cause x371 is needed in a reg for other than x372, namely all: , x372, x373, size: 2
shr r13, 56; x372 <- x371>> 56
mov rcx, rdi; x376, copying x370 here, cause x370 is needed in a reg for other than x376, namely all: , x375, x376, size: 2
and rcx, rdx; x376 <- x370&0xffffffffffffff
and r9, rdx; x366 <- x361&0xffffffffffffff
mov [ r14 + 0x0 ], rcx; out1[0] = x376
and rax, rdx; x373 <- x371&0xffffffffffffff
mov [ r14 + 0x20 ], rax; out1[4] = x373
mov [ r14 + 0x18 ], r11; out1[3] = x368
shr rdi, 56; x375 <- x370>> 56
mov [ r14 + 0x38 ], r9; out1[7] = x366
lea rdi, [ rdi + r15 ]
mov [ r14 + 0x8 ], rdi; out1[1] = x377
mov [ r14 + 0x30 ], rbx; out1[6] = x360
add r13, [ rsp + 0x210 ]
mov [ r14 + 0x28 ], r13; out1[5] = x374
mov rbx, [ rsp + 0x240 ]; restoring from stack
mov rbp, [ rsp + 0x248 ]; restoring from stack
mov r12, [ rsp + 0x250 ]; restoring from stack
mov r13, [ rsp + 0x258 ]; restoring from stack
mov r14, [ rsp + 0x260 ]; restoring from stack
mov r15, [ rsp + 0x268 ]; restoring from stack
add rsp, 0x270 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 159.12, best 104.06060606060606, lastGood 106.44615384615385
; seed 2797871388934122 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2584134 ms / 60000 runs=> 43.0689ms/run
; Time spent for assembling and measureing (initial batch_size=131, initial num_batches=101): 241771 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.09355977669888636
; number reverted permutation/ tried permutation: 22800 / 29982 =76.046%
; number reverted decision/ tried decision: 22216 / 30019 =74.006%