SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x2b0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x280 ], rbx; saving to stack
mov [ rsp + 0x288 ], rbp; saving to stack
mov [ rsp + 0x290 ], r12; saving to stack
mov [ rsp + 0x298 ], r13; saving to stack
mov [ rsp + 0x2a0 ], r14; saving to stack
mov [ rsp + 0x2a8 ], r15; saving to stack
mov rax, [ rsi + 0x28 ]; load m64 x12 to register64
mov r10, [ rsi + 0x30 ]; load m64 x7 to register64
mov r11, [ rsi + 0x38 ]; load m64 x1 to register64
mov rbx, [ rsi + 0x38 ]; load m64 x2 to register64
imul rbp, r11, 0x2; x3 <- x1 * 0x2
imul r12, r10, 0x2; x9 <- x7 * 0x2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, r14, r12; x91, x90<- arg1[2] * x9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r15, rcx, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x30 ]; load m64 x6 to register64
imul r8, rbx, 0x2; x4 <- x2 * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x30 ]; x27, x26<- arg1[6] * x6
mov [ rsp + 0x8 ], r11; spilling x1 to mem
mov r11, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x10 ], r10; spilling x7 to mem
mov [ rsp + 0x18 ], r15; spilling x133 to mem
mulx r10, r15, r8; x103, x102<- arg1[1] * x4
imul rdx, rax, 0x2; x14 <- x12 * 0x2
mov [ rsp + 0x20 ], r10; spilling x103 to mem
mov r10, [ rsi + 0x20 ]; load m64 x17 to register64
mov [ rsp + 0x28 ], r13; spilling x91 to mem
mov r13, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x30 ], r9; spilling x27 to mem
mulx r10, r9, r10; x67, x66<- arg1[4] * x17
mov rdx, rbp; x3 to rdx
mov [ rsp + 0x38 ], r12; spilling x9 to mem
mulx rbp, r12, [ rsi + 0x28 ]; x29, x28<- arg1[5] * x3
test al, al
adox rdi, r12
adcx rdi, r9
mov r9, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x40 ], r10; spilling x67 to mem
mulx r12, r10, r13; x79, x78<- arg1[3] * x14
setc dl; spill CF x309 to reg (rdx)
clc;
adcx rdi, r10
setc r10b; spill CF x313 to reg (r10)
mov [ rsp + 0x48 ], r12; spilling x79 to mem
seto r12b; spill OF x305 to reg (r12)
mov byte [ rsp + 0x50 ], dl; spilling byte x309 to mem
imul rdx, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
add rdi, r14; could be done better, if r0 has been u8 as well
setc r14b; spill CF x317 to reg (r14)
mov [ rsp + 0x58 ], rbx; spilling x2 to mem
imul rbx, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov byte [ rsp + 0x60 ], r14b; spilling byte x317 to mem
imul r14, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov byte [ rsp + 0x68 ], r10b; spilling byte x313 to mem
mov r10, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x70 ], rbp; spilling x29 to mem
mulx r14, rbp, r14; x119, x118<- arg1[0] * x5
test al, al
adox rdi, r15
adcx rdi, rcx
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r15, rbx; x95, x94<- arg1[2] * x15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x78 ], rdi; spilling x324 to mem
mov [ rsp + 0x80 ], r14; spilling x119 to mem
mulx rdi, r14, r10; x107, x106<- arg1[1] * x10
mov rdx, r9; x3 to rdx
mov [ rsp + 0x88 ], r8; spilling x4 to mem
mulx r9, r8, [ rsi + 0x20 ]; x57, x56<- arg1[4] * x3
mov [ rsp + 0x90 ], rax; spilling x12 to mem
setc al; spill CF x325 to reg (rax)
mov [ rsp + 0x98 ], rdi; spilling x107 to mem
seto dil; spill OF x321 to reg (rdi)
mov [ rsp + 0xa0 ], rbp; spilling x118 to mem
imul rbp, r11, 0x2; x8 <- x6 * 0x2
mov byte [ rsp + 0xa8 ], al; spilling byte x325 to mem
mov rax, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0xb0 ], dil; spilling byte x321 to mem
mov byte [ rsp + 0xb8 ], r12b; spilling byte x305 to mem
mulx rdi, r12, rbp; x49, x48<- arg1[5] * x8
imul rdx, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
add r12, r8; could be done better, if r0 has been u8 as well
mov [ rsp + 0xc0 ], r14; spilling x106 to mem
mulx r8, r14, [ rsi + 0x18 ]; x83, x82<- arg1[3] * x18
adcx r9, rdi
add r12, r14; could be done better, if r0 has been u8 as well
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r15
adcx r8, r9
adox rcx, r8
xor r15, r15
adox r12, [ rsp + 0xc0 ]
mov r14, [ rsp + 0x30 ]; load m64 x27 to register64
movzx r9, byte [ rsp + 0xb8 ]; load byte memx305 to register64
lea r14, [ r9 + r14 ]
adcx r14, [ rsp + 0x70 ]
clc;
adcx r12, [ rsp + 0xa0 ]
adox rcx, [ rsp + 0x98 ]
movzx r9, byte [ rsp + 0x50 ]; load byte memx309 to register64
lea r14, [ r9 + r14 ]
mov r9, [ rsp + 0x40 ]
lea r14, [r9+r14]
adcx rcx, [ rsp + 0x80 ]
mov r9, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r8, r15, [ rsp + 0x38 ]; x47, x46<- arg1[5] * x9
imul rdx, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
mov [ rsp + 0xc8 ], r13; spilling x14 to mem
mulx rdi, r13, [ rsi + 0x0 ]; x127, x126<- arg1[0] * x19
mov [ rsp + 0xd0 ], rdi; spilling x127 to mem
mov rdi, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0xd8 ], r13; spilling x126 to mem
mov [ rsp + 0xe0 ], r8; spilling x47 to mem
mulx r13, r8, [ rsp + 0x88 ]; x55, x54<- arg1[4] * x4
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xe8 ], r13; spilling x55 to mem
mov [ rsp + 0xf0 ], r15; spilling x46 to mem
mulx r13, r15, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
mov rdx, r12; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x332, x331, size: 2
shrd rdx, rcx, 56; x331 <- x166||x164 >> 56
mov rcx, rdx; x338, copying x331 here, cause x331 is needed in a reg for other than x338, namely all: , x333--x334, x338--x339, size: 2
mov [ rsp + 0xf8 ], r13; spilling x101 to mem
xor r13, r13
adox rcx, [ rsp + 0x78 ]
movzx r13, byte [ rsp + 0x68 ]; load byte memx313 to register64
lea r14, [ r13 + r14 ]
adcx r14, [ rsp + 0x48 ]
xchg rdx, r9; x18, swapping with x331, which is currently in rdx
mov [ rsp + 0x100 ], rcx; spilling x338 to mem
mulx r13, rcx, [ rsi + 0x0 ]; x125, x124<- arg1[0] * x18
clc;
adcx r8, [ rsp + 0xf0 ]
xchg rdx, rdi; x19, swapping with x18, which is currently in rdx
mov [ rsp + 0x108 ], r13; spilling x125 to mem
mov [ rsp + 0x110 ], rcx; spilling x124 to mem
mulx r13, rcx, [ rsi + 0x8 ]; x113, x112<- arg1[1] * x19
mov [ rsp + 0x118 ], r13; spilling x113 to mem
mov r13, [ rsp + 0xe0 ]; load m64 x47 to register64
adcx r13, [ rsp + 0xe8 ]
mov [ rsp + 0x120 ], rcx; spilling x112 to mem
movzx rcx, byte [ rsp + 0x60 ]; load byte memx317 to register64
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x28 ]
lea r14, [rcx+r14]
movzx rcx, byte [ rsp + 0xb0 ]; load byte memx321 to register64
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x20 ]
lea r14, [rcx+r14]
movzx rcx, byte [ rsp + 0xa8 ]; load byte memx325 to register64
lea r14, [ rcx + r14 ]
mov rcx, [ rsp + 0x18 ]
lea r14, [rcx+r14]
mov rcx, 0x0 ; moving imm to reg
adox r14, rcx
imul rcx, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
xchg rdx, rcx; x20, swapping with x19, which is currently in rdx
mov [ rsp + 0x128 ], r14; spilling x340 to mem
mov [ rsp + 0x130 ], r15; spilling x100 to mem
mulx r14, r15, [ rsi + 0x8 ]; x115, x114<- arg1[1] * x20
add r8, r15; could be done better, if r0 has been u8 as well
mov r15, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x138 ], r8; spilling x138 to mem
mov [ rsp + 0x140 ], r13; spilling x136 to mem
mulx r8, r13, rax; x105, x104<- arg1[1] * x3
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x148 ], r8; spilling x105 to mem
mov [ rsp + 0x150 ], r13; spilling x104 to mem
mulx r8, r13, rbp; x93, x92<- arg1[2] * x8
adcx r14, [ rsp + 0x140 ]
mov rdx, [ rsi + 0x20 ]; load m64 x16 to register64
mov [ rsp + 0x158 ], r8; spilling x93 to mem
mov r8, [ rsp + 0x138 ]; load m64 x138 to register64
test al, al
adox r8, [ rsp + 0xd8 ]
adox r14, [ rsp + 0xd0 ]
mov [ rsp + 0x160 ], r13; spilling x92 to mem
mov r13, r8; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd r13, r14, 56; x146 <- x144||x142 >> 56
mov r14, [ rsi + 0x28 ]; load m64 x11 to register64
mov [ rsp + 0x168 ], r13; spilling x146 to mem
imul r13, r14, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x170 ], r14; spilling x11 to mem
mov r14, rdx; preserving value of x16 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x178 ], r8; spilling x142 to mem
mov [ rsp + 0x180 ], r15; spilling x20 to mem
mulx r8, r15, r13; x81, x80<- arg1[3] * x13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x188 ], rbx; spilling x15 to mem
mov [ rsp + 0x190 ], r8; spilling x81 to mem
mulx rbx, r8, [ rsp + 0x10 ]; x43, x42<- arg1[6] * x7
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x198 ], r15; spilling x80 to mem
mulx r14, r15, r14; x69, x68<- arg1[4] * x16
mov rdx, r11; x6 to rdx
mulx rdx, r11, [ rsi + 0x30 ]; x35, x34<- arg1[6] * x6
xchg rdx, rax; x3, swapping with x35, which is currently in rdx
mov [ rsp + 0x1a0 ], r10; spilling x10 to mem
mov [ rsp + 0x1a8 ], r14; spilling x69 to mem
mulx r10, r14, [ rsi + 0x28 ]; x37, x36<- arg1[5] * x3
add r11, r14; could be done better, if r0 has been u8 as well
adcx r10, rax
add r11, r8; could be done better, if r0 has been u8 as well
mov r8, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rax, r14, [ rsp + 0x88 ]; x45, x44<- arg1[5] * x4
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r14
adcx rbx, r10
clc;
adcx r11, r15
setc r15b; spill CF x241 to reg (r15)
clc;
adcx r11, [ rsp + 0x198 ]
setc r10b; spill CF x245 to reg (r10)
clc;
adcx r11, [ rsp + 0x160 ]
setc r14b; spill CF x249 to reg (r14)
clc;
adcx r11, [ rsp + 0x130 ]
adox rax, rbx
movzx r15, r15b
lea rax, [ r15 + rax ]
mov r15, [ rsp + 0x1a8 ]
lea rax, [r15+rax]
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r11, [ rsp + 0x150 ]
movzx r10, r10b
lea rax, [ r10 + rax ]
mov r10, [ rsp + 0x190 ]
lea rax, [r10+rax]
movzx r14, r14b
lea rax, [ r14 + rax ]
mov r14, [ rsp + 0x158 ]
lea rax, [r14+rax]
adcx rax, [ rsp + 0xf8 ]
adox rax, [ rsp + 0x148 ]
xor rbx, rbx
adox r11, [ rsp + 0x120 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, r10, r8; x89, x88<- arg1[2] * x3
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r14, rbx, [ rsp + 0x88 ]; x41, x40<- arg1[6] * x4
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x1b0 ], r15; spilling x89 to mem
mov [ rsp + 0x1b8 ], r10; spilling x88 to mem
mulx r15, r10, rdi; x111, x110<- arg1[1] * x18
adcx r11, [ rsp + 0x110 ]
adox rax, [ rsp + 0x118 ]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, [ rsp + 0x168 ]
mov rdx, rcx; x19 to rdx
mulx rdx, rcx, [ rsi + 0x10 ]; x99, x98<- arg1[2] * x19
adcx rax, [ rsp + 0x108 ]
clc;
adcx r9, r11
mov r11, 0x0 ; moving imm to reg
adox rax, r11
mov r11, rdx; preserving value of x99 into a new reg
mov rdx, [ rsp + 0x188 ]; saving x15 in rdx.
mov [ rsp + 0x1c0 ], r15; spilling x111 to mem
mov [ rsp + 0x1c8 ], r10; spilling x110 to mem
mulx r15, r10, [ rsi + 0x0 ]; x123, x122<- arg1[0] * x15
mov [ rsp + 0x1d0 ], r15; spilling x123 to mem
mulx rdx, r15, [ rsi + 0x8 ]; x109, x108<- arg1[1] * x15
adc rax, 0x0
mov [ rsp + 0x1d8 ], rdx; spilling x109 to mem
mov rdx, r9; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x337, x336, size: 2
shrd rdx, rax, 56; x336 <- x335||x333 >> 56
mov rax, rdx; preserving value of x336 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x1e0 ], r15; spilling x108 to mem
mov [ rsp + 0x1e8 ], r10; spilling x122 to mem
mulx r15, r10, r8; x33, x32<- arg1[6] * x3
xor rdx, rdx
adox r10, rbx
xchg rdx, rbp; x8, swapping with 0x0, which is currently in rdx
mulx rbx, rbp, [ rsi + 0x18 ]; x77, x76<- arg1[3] * x8
adox r14, r15
xchg rdx, r13; x13, swapping with x8, which is currently in rdx
mulx rdx, r15, [ rsi + 0x20 ]; x65, x64<- arg1[4] * x13
adcx r10, r15
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rbp
adcx rdx, r14
clc;
adcx r10, [ rsp + 0x1b8 ]
adox rbx, rdx
adcx rbx, [ rsp + 0x1b0 ]
xor rbp, rbp
adox r10, rcx
adox r11, rbx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, r14, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
adcx r10, [ rsp + 0x1c8 ]
adcx r11, [ rsp + 0x1c0 ]
mov rdx, [ rsp + 0x58 ]; x2 to rdx
mulx rdx, rbx, [ rsi + 0x38 ]; x39, x38<- arg1[7] * x2
test al, al
adox r10, [ rsp + 0x1e8 ]
adox r11, [ rsp + 0x1d0 ]
mov rbp, rdx; preserving value of x39 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x1f0 ], rcx; spilling x85 to mem
mulx r15, rcx, r8; x73, x72<- arg1[3] * x3
adcx r10, rax
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1f8 ], r14; spilling x84 to mem
mulx rax, r14, [ rsp + 0x8 ]; x31, x30<- arg1[7] * x1
adc r11, 0x0
mov rdx, r10; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x349, x350, size: 2
shrd rdx, r11, 56; x349 <- x343||x341 >> 56
mov r11, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x200 ], rdx; spilling x349 to mem
mov rdx, [ rsp + 0x100 ]; x345, copying x338 here, cause x338 is needed in a reg for other than x345, namely all: , x345, x344, size: 2
and rdx, r11; x345 <- x338&0xffffffffffffff
mov r11, rdx; preserving value of x345 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x208 ], r15; spilling x73 to mem
mulx r13, r15, r13; x61, x60<- arg1[4] * x8
mov rdx, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x210 ], r11; spilling x345 to mem
mov r11, [ rsp + 0x178 ]; x147, copying x142 here, cause x142 is needed in a reg for other than x147, namely all: , x147, size: 1
and r11, rdx; x147 <- x142&0xffffffffffffff
adox r14, rbx
mov rbx, rdx; preserving value of 0xffffffffffffff into a new reg
mov rdx, [ rsp + 0x170 ]; saving x11 in rdx.
mov [ rsp + 0x218 ], r11; spilling x147 to mem
mulx rdx, r11, [ rsi + 0x28 ]; x53, x52<- arg1[5] * x11
adox rbp, rax
adcx r14, r11
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r15
xchg rdx, rdi; x18, swapping with x53, which is currently in rdx
mulx rdx, r15, [ rsi + 0x10 ]; x97, x96<- arg1[2] * x18
adcx rdi, rbp
clc;
adcx r14, rcx
adox r13, rdi
adcx r13, [ rsp + 0x208 ]
add r14, [ rsp + 0x1f8 ]; could be done better, if r0 has been u8 as well
mov rcx, rdx; preserving value of x97 into a new reg
mov rdx, [ rsp + 0x1a0 ]; saving x10 in rdx.
mulx rdx, r11, [ rsi + 0x0 ]; x121, x120<- arg1[0] * x10
adcx r13, [ rsp + 0x1f0 ]
test al, al
adox r14, r15
adox rcx, r13
adcx r14, [ rsp + 0x1e0 ]
adcx rcx, [ rsp + 0x1d8 ]
imul rbp, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
xchg rdx, r8; x3, swapping with x121, which is currently in rdx
mulx rdx, r15, [ rsi + 0x30 ]; x25, x24<- arg1[6] * x3
xor rdi, rdi
adox r14, r11
xchg rdx, rbp; x21, swapping with x25, which is currently in rdx
mulx rdx, r11, [ rsi + 0x0 ]; x131, x130<- arg1[0] * x21
adox r8, rcx
adcx r14, [ rsp + 0x200 ]
adc r8, 0x0
and r12, rbx; x332 <- x164&0xffffffffffffff
mov r13, r14; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x359, x360, size: 2
shrd r13, r8, 56; x359 <- x353||x351 >> 56
lea r13, [ r13 + r12 ]
mov rcx, r13; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, x366, size: 2
shr rcx, 56; x365 <- x361>> 56
mov r8, rcx; x370, copying x365 here, cause x365 is needed in a reg for other than x370, namely all: , x369, x370, size: 2
add r8, [ rsp + 0x210 ]
mov r12, r8; x376, copying x370 here, cause x370 is needed in a reg for other than x376, namely all: , x376, x375, size: 2
and r12, rbx; x376 <- x370&0xffffffffffffff
mov rdi, rdx; preserving value of x131 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rax, rbx, [ rsp + 0x38 ]; x75, x74<- arg1[3] * x9
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x0 ], r12; out1[0] = x376
mov r12, rdx; preserving value of out1 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x220 ], rdi; spilling x131 to mem
mov [ rsp + 0x228 ], r11; spilling x130 to mem
mulx rdi, r11, [ rsp + 0xc8 ]; x63, x62<- arg1[4] * x14
mov rdx, [ rsp + 0x100 ]; load m64 x338 to register64
mov [ rsp + 0x0 ], r12; spilling out1 to mem
mov r12, [ rsp + 0x128 ]; load m64 x340 to register64
shrd rdx, r12, 56; x344 <- x340||x338 >> 56
mov r12, rdx; preserving value of x344 into a new reg
mov rdx, [ rsp + 0x88 ]; saving x4 in rdx.
mov [ rsp + 0x230 ], rax; spilling x75 to mem
mov [ rsp + 0x238 ], rbx; spilling x74 to mem
mulx rax, rbx, [ rsi + 0x10 ]; x87, x86<- arg1[2] * x4
test al, al
adox r15, r11
mov r11, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x240 ], r12; spilling x344 to mem
mov [ rsp + 0x248 ], rax; spilling x87 to mem
mulx r12, rax, [ rsp + 0x8 ]; x23, x22<- arg1[7] * x1
adox rdi, rbp
mov rdx, r11; x4 to rdx
mulx rdx, r11, [ rsi + 0x18 ]; x71, x70<- arg1[3] * x4
mov rbp, rdx; preserving value of x71 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x250 ], r11; spilling x70 to mem
mov [ rsp + 0x258 ], r12; spilling x23 to mem
mulx r11, r12, [ rsp + 0x38 ]; x59, x58<- arg1[4] * x9
adcx r15, [ rsp + 0x238 ]
adcx rdi, [ rsp + 0x230 ]
xor rdx, rdx
adox r15, rbx
adox rdi, [ rsp + 0x248 ]
mov rbx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsp + 0x180 ]; saving x20 in rdx.
mov [ rsp + 0x260 ], rbp; spilling x71 to mem
mulx rdx, rbp, [ rsi + 0x0 ]; x129, x128<- arg1[0] * x20
adcx r15, [ rsp + 0x228 ]
adcx rdi, [ rsp + 0x220 ]
mov [ rsp + 0x268 ], rdx; spilling x129 to mem
xor rdx, rdx
adox r15, [ rsp + 0x240 ]
mov rbx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x270 ], rbp; spilling x128 to mem
mov [ rsp + 0x278 ], r11; spilling x59 to mem
mulx rbp, r11, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
mov rdx, [ rsp + 0x90 ]; x12 to rdx
mulx rdx, rbx, [ rsi + 0x28 ]; x51, x50<- arg1[5] * x12
adcx rax, rbx
mov rbx, 0x0 ; moving imm to reg
adox rdi, rbx
adcx rdx, [ rsp + 0x258 ]
mov rbx, r15; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x355, x354, size: 2
shrd rbx, rdi, 56; x354 <- x348||x346 >> 56
add rax, r12; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, [ rsp + 0x250 ]
adcx rdx, [ rsp + 0x278 ]
clc;
adcx rax, r11
adox rdx, [ rsp + 0x260 ]
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rax, [ rsp + 0x270 ]
adcx rbp, rdx
clc;
adcx rax, rbx
adox rbp, [ rsp + 0x268 ]
adc rbp, 0x0
mov r11, rax; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x362, x363, size: 2
shrd r11, rbp, 56; x362 <- x358||x356 >> 56
mov rdi, 0xffffffffffffff ; moving imm to reg
and r15, rdi; x355 <- x346&0xffffffffffffff
shr r8, 56; x375 <- x370>> 56
add r11, [ rsp + 0x218 ]
mov rbx, r11; x368, copying x364 here, cause x364 is needed in a reg for other than x368, namely all: , x367, x368, size: 2
and rbx, rdi; x368 <- x364&0xffffffffffffff
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x18 ], rbx; out1[3] = x368
lea r8, [ r8 + r15 ]
shr r11, 56; x367 <- x364>> 56
and r10, rdi; x350 <- x341&0xffffffffffffff
and r9, rdi; x337 <- x333&0xffffffffffffff
lea r9, [ r9 + rcx ]
lea r11, [ r11 + r9 ]
mov rcx, r11; x372, copying x371 here, cause x371 is needed in a reg for other than x372, namely all: , x373, x372, size: 2
shr rcx, 56; x372 <- x371>> 56
and r11, rdi; x373 <- x371&0xffffffffffffff
and r13, rdi; x366 <- x361&0xffffffffffffff
and rax, rdi; x363 <- x356&0xffffffffffffff
mov [ rdx + 0x38 ], r13; out1[7] = x366
and r14, rdi; x360 <- x351&0xffffffffffffff
mov [ rdx + 0x30 ], r14; out1[6] = x360
lea rcx, [ rcx + r10 ]
mov [ rdx + 0x28 ], rcx; out1[5] = x374
mov [ rdx + 0x20 ], r11; out1[4] = x373
mov [ rdx + 0x8 ], r8; out1[1] = x377
mov [ rdx + 0x10 ], rax; out1[2] = x363
mov rbx, [ rsp + 0x280 ]; restoring from stack
mov rbp, [ rsp + 0x288 ]; restoring from stack
mov r12, [ rsp + 0x290 ]; restoring from stack
mov r13, [ rsp + 0x298 ]; restoring from stack
mov r14, [ rsp + 0x2a0 ]; restoring from stack
mov r15, [ rsp + 0x2a8 ]; restoring from stack
add rsp, 0x2b0 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 146.3, best 107.46875, lastGood 110.11023622047244
; seed 1926673388220806 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2019353 ms / 60000 runs=> 33.655883333333335ms/run
; Time spent for assembling and measureing (initial batch_size=128, initial num_batches=101): 184292 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.09126289460039924
; number reverted permutation/ tried permutation: 22197 / 30072 =73.813%
; number reverted decision/ tried decision: 21482 / 29929 =71.777%