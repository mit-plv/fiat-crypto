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
mov rax, [ rsi + 0x38 ]; load m64 x2 to register64
mov r10, [ rsi + 0x28 ]; load m64 x12 to register64
imul r11, rax, 0x2; x4 <- x2 * 0x2
mov rbx, [ rsi + 0x30 ]; load m64 x6 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r12, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r14, r11; x103, x102<- arg1[1] * x4
imul r15, rbx, 0x2; x8 <- x6 * 0x2
imul rdx, r10, 0x2; x14 <- x12 * 0x2
mov rcx, [ rsi + 0x38 ]; load m64 x1 to register64
mov r8, [ rsi + 0x30 ]; load m64 x7 to register64
imul r9, r8, 0x2; x9 <- x7 * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], rax; spilling x2 to mem
mulx rdi, rax, [ rsi + 0x18 ]; x79, x78<- arg1[3] * x14
mov [ rsp + 0x10 ], rbp; spilling x133 to mem
mov rbp, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x18 ], r13; spilling x103 to mem
mov [ rsp + 0x20 ], rdi; spilling x79 to mem
mulx r13, rdi, r9; x91, x90<- arg1[2] * x9
imul rdx, rcx, 0x2; x3 <- x1 * 0x2
mov [ rsp + 0x28 ], r13; spilling x91 to mem
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x30 ], r12; spilling x132 to mem
mov [ rsp + 0x38 ], r15; spilling x8 to mem
mulx r12, r15, rbx; x27, x26<- arg1[6] * x6
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x40 ], r11; spilling x4 to mem
mov [ rsp + 0x48 ], r12; spilling x27 to mem
mulx r11, r12, r13; x29, x28<- arg1[5] * x3
mov rdx, [ rsi + 0x20 ]; load m64 x17 to register64
add r15, r12; could be done better, if r0 has been u8 as well
mulx rdx, r12, [ rsi + 0x20 ]; x67, x66<- arg1[4] * x17
mov [ rsp + 0x50 ], r10; spilling x12 to mem
setc r10b; spill CF x305 to reg (r10)
mov [ rsp + 0x58 ], rdx; spilling x67 to mem
imul rdx, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov [ rsp + 0x60 ], r11; spilling x29 to mem
xor r11, r11
adox r15, r12
mulx rdx, r12, [ rsi + 0x0 ]; x119, x118<- arg1[0] * x5
adcx r15, rax
setc al; spill CF x313 to reg (rax)
seto r11b; spill OF x309 to reg (r11)
mov [ rsp + 0x68 ], rdx; spilling x119 to mem
imul rdx, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
mov [ rsp + 0x70 ], r8; spilling x7 to mem
xor r8, r8
adox r15, rdi
mulx rdi, r8, [ rsi + 0x8 ]; x107, x106<- arg1[1] * x10
adcx r15, r14
mov r14, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x78 ], al; spilling byte x313 to mem
mov [ rsp + 0x80 ], r12; spilling x118 to mem
mulx rax, r12, [ rsp + 0x38 ]; x49, x48<- arg1[5] * x8
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x88 ], rbp; spilling x14 to mem
mov byte [ rsp + 0x90 ], r11b; spilling byte x309 to mem
mulx rbp, r11, r13; x57, x56<- arg1[4] * x3
setc dl; spill CF x321 to reg (rdx)
mov byte [ rsp + 0x98 ], r10b; spilling byte x305 to mem
seto r10b; spill OF x317 to reg (r10)
mov [ rsp + 0xa0 ], rdi; spilling x107 to mem
imul rdi, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
add r15, [ rsp + 0x30 ]; could be done better, if r0 has been u8 as well
mov [ rsp + 0xa8 ], r15; spilling x324 to mem
setc r15b; spill CF x325 to reg (r15)
mov [ rsp + 0xb0 ], r9; spilling x9 to mem
imul r9, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
add r12, r11; could be done better, if r0 has been u8 as well
adcx rbp, rax
mov al, dl; preserving value of x321 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xb8 ], rcx; spilling x1 to mem
mulx r11, rcx, rdi; x95, x94<- arg1[2] * x15
mov rdx, r9; x18 to rdx
mov byte [ rsp + 0xc0 ], r15b; spilling byte x325 to mem
mulx r9, r15, [ rsi + 0x18 ]; x83, x82<- arg1[3] * x18
add r12, r15; could be done better, if r0 has been u8 as well
adcx r9, rbp
xor rbp, rbp
adox r12, rcx
adcx r12, r8
adox r11, r9
adcx r11, [ rsp + 0xa0 ]
mov r8, [ rsp + 0x48 ]; load m64 x27 to register64
sar byte [ rsp + 0x98 ], 1
adcx r8, [ rsp + 0x60 ]
sar byte [ rsp + 0x90 ], 1
adcx r8, [ rsp + 0x58 ]
adox r12, [ rsp + 0x80 ]
adox r11, [ rsp + 0x68 ]
mov rcx, r12; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x331, x332, size: 2
shrd rcx, r11, 56; x331 <- x166||x164 >> 56
sar byte [ rsp + 0x78 ], 1
adcx r8, [ rsp + 0x20 ]
sar  r10b, 1
adcx r8, [ rsp + 0x28 ]
sar  al, 1
adcx r8, [ rsp + 0x18 ]
imul r10, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
mov rax, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r15, r9, [ rsp + 0xb0 ]; x75, x74<- arg1[3] * x9
sar byte [ rsp + 0xc0 ], 1
adcx r8, [ rsp + 0x10 ]
mov rdx, rcx; x338, copying x331 here, cause x331 is needed in a reg for other than x338, namely all: , x338--x339, x333--x334, size: 2
adox rdx, [ rsp + 0xa8 ]
adox r8, rbp
mov r11, rdx; preserving value of x338 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xc8 ], rbx; spilling x6 to mem
mulx rbp, rbx, [ rsp + 0x40 ]; x87, x86<- arg1[2] * x4
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xd0 ], rbp; spilling x87 to mem
mulx r10, rbp, r10; x131, x130<- arg1[0] * x21
mov rdx, r11; x344, copying x338 here, cause x338 is needed in a reg for other than x344, namely all: , x345, x344, size: 2
shrd rdx, r8, 56; x344 <- x340||x338 >> 56
mov r8, rdx; preserving value of x344 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0xd8 ], r10; spilling x131 to mem
mov [ rsp + 0xe0 ], rbp; spilling x130 to mem
mulx r10, rbp, r13; x25, x24<- arg1[6] * x3
mov rdx, [ rsp + 0x88 ]; x14 to rdx
mov [ rsp + 0xe8 ], r8; spilling x344 to mem
mulx rdx, r8, [ rsi + 0x20 ]; x63, x62<- arg1[4] * x14
add rbp, r8; could be done better, if r0 has been u8 as well
adcx rdx, r10
xor r10, r10
adox rbp, r9
adox r15, rdx
adcx rbp, rbx
adcx r15, [ rsp + 0xd0 ]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r9, rbx, [ rsp + 0xb8 ]; x23, x22<- arg1[7] * x1
test al, al
adox rbp, [ rsp + 0xe0 ]
adox r15, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, r10, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
adcx rbp, [ rsp + 0xe8 ]
adc r15, 0x0
imul rdx, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov [ rsp + 0xf0 ], r14; spilling x10 to mem
mov [ rsp + 0xf8 ], r8; spilling x117 to mem
mulx r14, r8, [ rsi + 0x0 ]; x129, x128<- arg1[0] * x20
mov [ rsp + 0x100 ], r14; spilling x129 to mem
mov r14, rbp; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x355, x354, size: 2
shrd r14, r15, 56; x354 <- x348||x346 >> 56
mov r15, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x108 ], r14; spilling x354 to mem
mov [ rsp + 0x110 ], r8; spilling x128 to mem
mulx r14, r8, [ rsp + 0xb0 ]; x59, x58<- arg1[4] * x9
mov rdx, [ rsp + 0x50 ]; x12 to rdx
mov [ rsp + 0x118 ], r10; spilling x116 to mem
mulx rdx, r10, [ rsi + 0x28 ]; x51, x50<- arg1[5] * x12
add rbx, r10; could be done better, if r0 has been u8 as well
adcx rdx, r9
add rbx, r8; could be done better, if r0 has been u8 as well
adcx r14, rdx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r8, [ rsp + 0x40 ]; x71, x70<- arg1[3] * x4
xor rdx, rdx
adox rbx, r8
adox r9, r14
adcx rbx, [ rsp + 0x118 ]
adcx r9, [ rsp + 0xf8 ]
xor r10, r10
adox rbx, [ rsp + 0x110 ]
adcx rbx, [ rsp + 0x108 ]
adox r9, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, r8, [ rsp + 0x40 ]; x55, x54<- arg1[4] * x4
adc r9, 0x0
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x120 ], r14; spilling x55 to mem
mulx r10, r14, [ rsp + 0xb0 ]; x47, x46<- arg1[5] * x9
mov rdx, rbx; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x363, x362, size: 2
shrd rdx, r9, 56; x362 <- x358||x356 >> 56
imul r9, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
mov [ rsp + 0x128 ], rdx; spilling x362 to mem
mov rdx, 0xffffffffffffff ; moving imm to reg
and r11, rdx; x345 <- x338&0xffffffffffffff
adox r14, r8
mov r8, rdx; preserving value of 0xffffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x130 ], r11; spilling x345 to mem
mov [ rsp + 0x138 ], rdi; spilling x15 to mem
mulx r11, rdi, r9; x127, x126<- arg1[0] * x19
mov rdx, r15; x20 to rdx
mulx rdx, r15, [ rsi + 0x8 ]; x115, x114<- arg1[1] * x20
adcx r14, r15
setc r15b; spill CF x139 to reg (r15)
clc;
adcx r14, rdi
adox r10, [ rsp + 0x120 ]
setc dil; spill CF x143 to reg (rdi)
mov [ rsp + 0x140 ], rax; spilling x18 to mem
mov rax, r14; x147, copying x142 here, cause x142 is needed in a reg for other than x147, namely all: , x147, x146, size: 2
and rax, r8; x147 <- x142&0xffffffffffffff
add rax, [ rsp + 0x128 ]
sar  r15b, 1
adcx rdx, r10
mov r15, rax; x368, copying x364 here, cause x364 is needed in a reg for other than x368, namely all: , x367, x368, size: 2
and r15, r8; x368 <- x364&0xffffffffffffff
sar  dil, 1
adcx r11, rdx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r10, r9; x113, x112<- arg1[1] * x19
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x148 ], r15; spilling x368 to mem
mulx r8, r15, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x150 ], rdi; spilling x113 to mem
mov [ rsp + 0x158 ], r10; spilling x112 to mem
mulx rdi, r10, r13; x105, x104<- arg1[1] * x3
mov rdx, [ rsi + 0x28 ]; load m64 x11 to register64
shrd r14, r11, 56; x146 <- x144||x142 >> 56
imul r11, rdx, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x160 ], r14; spilling x146 to mem
mov r14, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x168 ], rdi; spilling x105 to mem
mov [ rsp + 0x170 ], r10; spilling x104 to mem
mulx rdi, r10, [ rsp + 0x140 ]; x125, x124<- arg1[0] * x18
mov rdx, r11; x13 to rdx
mov [ rsp + 0x178 ], rdi; spilling x125 to mem
mulx r11, rdi, [ rsi + 0x18 ]; x81, x80<- arg1[3] * x13
mov [ rsp + 0x180 ], r10; spilling x124 to mem
mov r10, [ rsi + 0x20 ]; load m64 x16 to register64
mov [ rsp + 0x188 ], r8; spilling x101 to mem
mov r8, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x190 ], r15; spilling x100 to mem
mov [ rsp + 0x198 ], r11; spilling x81 to mem
mulx r15, r11, r13; x37, x36<- arg1[5] * x3
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1a0 ], rdi; spilling x80 to mem
mov [ rsp + 0x1a8 ], r15; spilling x37 to mem
mulx rdi, r15, [ rsp + 0x40 ]; x45, x44<- arg1[5] * x4
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1b0 ], rdi; spilling x45 to mem
mov [ rsp + 0x1b8 ], r15; spilling x44 to mem
mulx rdi, r15, [ rsp + 0x70 ]; x43, x42<- arg1[6] * x7
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1c0 ], rdi; spilling x43 to mem
mov [ rsp + 0x1c8 ], r15; spilling x42 to mem
mulx rdi, r15, [ rsp + 0x38 ]; x93, x92<- arg1[2] * x8
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x1d0 ], rdi; spilling x93 to mem
mulx r10, rdi, r10; x69, x68<- arg1[4] * x16
mov rdx, [ rsp + 0xc8 ]; x6 to rdx
mov [ rsp + 0x1d8 ], r15; spilling x92 to mem
mulx rdx, r15, [ rsi + 0x30 ]; x35, x34<- arg1[6] * x6
add r15, r11; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x1a8 ]
add r15, [ rsp + 0x1c8 ]; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x1c0 ]
add r15, [ rsp + 0x1b8 ]; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x1b0 ]
test al, al
adox r15, rdi
adox r10, rdx
adcx r15, [ rsp + 0x1a0 ]
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x1d8 ]
adcx r10, [ rsp + 0x198 ]
clc;
adcx r15, [ rsp + 0x190 ]
adox r10, [ rsp + 0x1d0 ]
adcx r10, [ rsp + 0x188 ]
test al, al
adox r15, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, r11, [ rsp + 0x38 ]; x77, x76<- arg1[3] * x8
adcx r15, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1e0 ], r12; spilling x164 to mem
mov [ rsp + 0x1e8 ], rdi; spilling x77 to mem
mulx r12, rdi, r13; x89, x88<- arg1[2] * x3
adox r10, [ rsp + 0x168 ]
adcx r10, [ rsp + 0x150 ]
add r15, [ rsp + 0x180 ]; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x178 ]
xor rdx, rdx
adox r15, [ rsp + 0x160 ]
mov [ rsp + 0x1f0 ], r12; spilling x89 to mem
mov r12, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x1f8 ], rdi; spilling x88 to mem
mov [ rsp + 0x200 ], r11; spilling x76 to mem
mulx rdi, r11, [ rsp + 0x40 ]; x41, x40<- arg1[6] * x4
adox r10, r12
adcx rcx, r15
adc r10, 0x0
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, r15, r8; x65, x64<- arg1[4] * x13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r12, r9; x99, x98<- arg1[2] * x19
mov rdx, rcx; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x337, x336, size: 2
shrd rdx, r10, 56; x336 <- x335||x333 >> 56
mov r10, rdx; preserving value of x336 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x208 ], r9; spilling x99 to mem
mov [ rsp + 0x210 ], r12; spilling x98 to mem
mulx r9, r12, r13; x33, x32<- arg1[6] * x3
add r12, r11; could be done better, if r0 has been u8 as well
adcx rdi, r9
add r12, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r11, r15, [ rsp + 0x140 ]; x111, x110<- arg1[1] * x18
mov rdx, [ rsp + 0x140 ]; x18 to rdx
mulx rdx, r9, [ rsi + 0x10 ]; x97, x96<- arg1[2] * x18
adcx r8, rdi
add r12, [ rsp + 0x200 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x1e8 ]
add r12, [ rsp + 0x1f8 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x1f0 ]
xor rdi, rdi
adox r12, [ rsp + 0x210 ]
adcx r12, r15
adox r8, [ rsp + 0x208 ]
adcx r11, r8
mov r15, rdx; preserving value of x97 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx r8, rdi, [ rsp + 0xb8 ]; x31, x30<- arg1[7] * x1
mov rdx, [ rsp + 0x138 ]; x15 to rdx
mov [ rsp + 0x218 ], r15; spilling x97 to mem
mov [ rsp + 0x220 ], r9; spilling x96 to mem
mulx r15, r9, [ rsi + 0x0 ]; x123, x122<- arg1[0] * x15
test al, al
adox r12, r9
adox r15, r11
adcx r12, r10
mulx rdx, r10, [ rsi + 0x8 ]; x109, x108<- arg1[1] * x15
mov r11, rdx; preserving value of x109 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x228 ], r10; spilling x108 to mem
mulx r9, r10, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x230 ], r11; spilling x109 to mem
mov [ rsp + 0x238 ], r9; spilling x85 to mem
mulx r11, r9, [ rsp + 0x8 ]; x39, x38<- arg1[7] * x2
adc r15, 0x0
mov rdx, r12; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd rdx, r15, 56; x349 <- x343||x341 >> 56
add rdi, r9; could be done better, if r0 has been u8 as well
mov r9, rdx; preserving value of x349 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx r14, r15, r14; x53, x52<- arg1[5] * x11
adcx r11, r8
add rdi, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r8, r13; x73, x72<- arg1[3] * x3
adcx r14, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, r11, [ rsp + 0x38 ]; x61, x60<- arg1[4] * x8
add rdi, r11; could be done better, if r0 has been u8 as well
adcx r15, r14
add rdi, r8; could be done better, if r0 has been u8 as well
mov rdx, [ rsp + 0xf0 ]; x10 to rdx
mulx rdx, r8, [ rsi + 0x0 ]; x121, x120<- arg1[0] * x10
adcx r13, r15
test al, al
adox rdi, r10
adcx rdi, [ rsp + 0x220 ]
adox r13, [ rsp + 0x238 ]
adcx r13, [ rsp + 0x218 ]
add rdi, [ rsp + 0x228 ]; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x230 ]
add rdi, r8; could be done better, if r0 has been u8 as well
adcx rdx, r13
add rdi, r9; could be done better, if r0 has been u8 as well
adc rdx, 0x0
mov r10, rdi; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x359, x360, size: 2
shrd r10, rdx, 56; x359 <- x353||x351 >> 56
mov r9, 0xffffffffffffff ; moving imm to reg
mov r14, [ rsp + 0x1e0 ]; x332, copying x164 here, cause x164 is needed in a reg for other than x332, namely all: , x332, size: 1
and r14, r9; x332 <- x164&0xffffffffffffff
lea r10, [ r10 + r14 ]
and rcx, r9; x337 <- x333&0xffffffffffffff
and rdi, r9; x360 <- x351&0xffffffffffffff
shr rax, 56; x367 <- x364>> 56
mov r11, r10; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, x366, size: 2
shr r11, 56; x365 <- x361>> 56
lea rcx, [ rcx + r11 ]
add r11, [ rsp + 0x130 ]
and rbp, r9; x355 <- x346&0xffffffffffffff
and r10, r9; x366 <- x361&0xffffffffffffff
lea rax, [ rax + rcx ]
mov r15, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r15 + 0x30 ], rdi; out1[6] = x360
mov [ r15 + 0x38 ], r10; out1[7] = x366
mov r8, r11; x375, copying x370 here, cause x370 is needed in a reg for other than x375, namely all: , x376, x375, size: 2
shr r8, 56; x375 <- x370>> 56
and r12, r9; x350 <- x341&0xffffffffffffff
mov r13, rax; x373, copying x371 here, cause x371 is needed in a reg for other than x373, namely all: , x372, x373, size: 2
and r13, r9; x373 <- x371&0xffffffffffffff
and r11, r9; x376 <- x370&0xffffffffffffff
lea r8, [ r8 + rbp ]
shr rax, 56; x372 <- x371>> 56
lea rax, [ rax + r12 ]
and rbx, r9; x363 <- x356&0xffffffffffffff
mov rdx, [ rsp + 0x148 ]; TMP = x368
mov [ r15 + 0x18 ], rdx; out1[3] = TMP
mov [ r15 + 0x10 ], rbx; out1[2] = x363
mov [ r15 + 0x8 ], r8; out1[1] = x377
mov [ r15 + 0x28 ], rax; out1[5] = x374
mov [ r15 + 0x20 ], r13; out1[4] = x373
mov [ r15 + 0x0 ], r11; out1[0] = x376
mov rbx, [ rsp + 0x240 ]; restoring from stack
mov rbp, [ rsp + 0x248 ]; restoring from stack
mov r12, [ rsp + 0x250 ]; restoring from stack
mov r13, [ rsp + 0x258 ]; restoring from stack
mov r14, [ rsp + 0x260 ]; restoring from stack
mov r15, [ rsp + 0x268 ]; restoring from stack
add rsp, 0x270 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 171.81, best 126.3125, lastGood 127.13541666666667
; seed 3468290092887263 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3176720 ms / 60000 runs=> 52.94533333333333ms/run
; Time spent for assembling and measureing (initial batch_size=96, initial num_batches=101): 235110 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.07401029993200534
; number reverted permutation/ tried permutation: 23709 / 29947 =79.170%
; number reverted decision/ tried decision: 23886 / 30054 =79.477%