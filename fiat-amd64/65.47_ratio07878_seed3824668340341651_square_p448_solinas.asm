SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x2a0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x270 ], rbx; saving to stack
mov [ rsp + 0x278 ], rbp; saving to stack
mov [ rsp + 0x280 ], r12; saving to stack
mov [ rsp + 0x288 ], r13; saving to stack
mov [ rsp + 0x290 ], r14; saving to stack
mov [ rsp + 0x298 ], r15; saving to stack
mov rax, [ rsi + 0x30 ]; load m64 x7 to register64
mov r10, [ rsi + 0x38 ]; load m64 x2 to register64
imul r11, r10, 0x2; x4 <- x2 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, r11; x103, x102<- arg1[1] * x4
imul r12, rax, 0x2; x9 <- x7 * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, r14, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
mov r15, [ rsi + 0x28 ]; load m64 x12 to register64
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r8, r12; x91, x90<- arg1[2] * x9
imul rdx, r15, 0x2; x14 <- x12 * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x18 ]; x79, x78<- arg1[3] * x14
mov [ rsp + 0x8 ], r13; spilling x133 to mem
mov r13, [ rsi + 0x20 ]; load m64 x17 to register64
mov [ rsp + 0x10 ], rbx; spilling x103 to mem
mov rbx, [ rsi + 0x38 ]; load m64 x1 to register64
mov [ rsp + 0x18 ], rcx; spilling x91 to mem
imul rcx, rbx, 0x2; x3 <- x1 * 0x2
mov [ rsp + 0x20 ], r9; spilling x79 to mem
mov r9, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x28 ], r10; spilling x2 to mem
mov [ rsp + 0x30 ], rax; spilling x7 to mem
mulx r10, rax, rcx; x29, x28<- arg1[5] * x3
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x38 ], r10; spilling x29 to mem
mulx r13, r10, r13; x67, x66<- arg1[4] * x17
mov rdx, [ rsi + 0x30 ]; load m64 x6 to register64
mov [ rsp + 0x40 ], r13; spilling x67 to mem
mov [ rsp + 0x48 ], r11; spilling x4 to mem
mulx r13, r11, [ rsi + 0x30 ]; x27, x26<- arg1[6] * x6
test al, al
adox r11, rax
adcx r11, r10
setc al; spill CF x309 to reg (rax)
clc;
adcx r11, rdi
seto dil; spill OF x305 to reg (rdi)
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r8
setc r8b; spill CF x313 to reg (r8)
clc;
adcx r11, rbp
setc bpl; spill CF x321 to reg (rbp)
seto r10b; spill OF x317 to reg (r10)
mov [ rsp + 0x50 ], r15; spilling x12 to mem
imul r15, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov byte [ rsp + 0x58 ], bpl; spilling byte x321 to mem
imul rbp, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
mov byte [ rsp + 0x60 ], r10b; spilling byte x317 to mem
mov r10, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov byte [ rsp + 0x68 ], r8b; spilling byte x313 to mem
mulx r15, r8, r15; x119, x118<- arg1[0] * x5
add r11, r14; could be done better, if r0 has been u8 as well
mov rdx, rbp; x10 to rdx
mulx rbp, r14, [ rsi + 0x8 ]; x107, x106<- arg1[1] * x10
mov [ rsp + 0x70 ], r9; spilling x14 to mem
setc r9b; spill CF x325 to reg (r9)
mov byte [ rsp + 0x78 ], al; spilling byte x309 to mem
imul rax, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov byte [ rsp + 0x80 ], r9b; spilling byte x325 to mem
imul r9, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
mov [ rsp + 0x88 ], r13; spilling x27 to mem
mov r13, rdx; preserving value of x10 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0x90 ], dil; spilling byte x305 to mem
mov [ rsp + 0x98 ], r12; spilling x9 to mem
mulx rdi, r12, rcx; x57, x56<- arg1[4] * x3
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xa0 ], rbx; spilling x1 to mem
mov [ rsp + 0xa8 ], r11; spilling x324 to mem
mulx rbx, r11, r9; x83, x82<- arg1[3] * x18
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xb0 ], r15; spilling x119 to mem
mov [ rsp + 0xb8 ], r8; spilling x118 to mem
mulx r15, r8, rax; x95, x94<- arg1[2] * x15
imul rdx, r10, 0x2; x8 <- x6 * 0x2
mov [ rsp + 0xc0 ], rbp; spilling x107 to mem
mov [ rsp + 0xc8 ], r15; spilling x95 to mem
mulx rbp, r15, [ rsi + 0x28 ]; x49, x48<- arg1[5] * x8
test al, al
adox r15, r12
adcx r15, r11
adox rdi, rbp
adcx rbx, rdi
xor r12, r12
adox r15, r8
adcx r15, r14
adox rbx, [ rsp + 0xc8 ]
adcx rbx, [ rsp + 0xc0 ]
add r15, [ rsp + 0xb8 ]; could be done better, if r0 has been u8 as well
adcx rbx, [ rsp + 0xb0 ]
mov r14, r15; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x331, x332, size: 2
shrd r14, rbx, 56; x331 <- x166||x164 >> 56
mov r11, r14; x338, copying x331 here, cause x331 is needed in a reg for other than x338, namely all: , x338--x339, x333--x334, size: 2
add r11, [ rsp + 0xa8 ]; could be done better, if r0 has been u8 as well
setc r8b; spill CF x339 to reg (r8)
imul rbp, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
imul rdi, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov rbx, 0xffffffffffffff ; moving imm to reg
mov r12, r11; x345, copying x338 here, cause x338 is needed in a reg for other than x345, namely all: , x344, x345, size: 2
and r12, rbx; x345 <- x338&0xffffffffffffff
mov rbx, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov byte [ rsp + 0xd0 ], r8b; spilling byte x339 to mem
mov [ rsp + 0xd8 ], r12; spilling x345 to mem
mulx r8, r12, [ rsp + 0x48 ]; x55, x54<- arg1[4] * x4
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xe0 ], rdi; spilling x20 to mem
mov [ rsp + 0xe8 ], r8; spilling x55 to mem
mulx rdi, r8, [ rsp + 0x98 ]; x47, x46<- arg1[5] * x9
adox r8, r12
mov rdx, rbp; x19 to rdx
mulx rbp, r12, [ rsi + 0x0 ]; x127, x126<- arg1[0] * x19
adox rdi, [ rsp + 0xe8 ]
mov [ rsp + 0xf0 ], rbp; spilling x127 to mem
mov rbp, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xf8 ], r12; spilling x126 to mem
mov [ rsp + 0x100 ], rdi; spilling x136 to mem
mulx r12, rdi, [ rsp + 0xe0 ]; x115, x114<- arg1[1] * x20
adcx r8, rdi
mov rdx, r9; x18 to rdx
mulx r9, rdi, [ rsi + 0x0 ]; x125, x124<- arg1[0] * x18
adcx r12, [ rsp + 0x100 ]
mov [ rsp + 0x108 ], r9; spilling x125 to mem
xor r9, r9
adox r8, [ rsp + 0xf8 ]
adox r12, [ rsp + 0xf0 ]
mov r9, r8; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x146, x147, size: 2
shrd r9, r12, 56; x146 <- x144||x142 >> 56
mov r12, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x110 ], r9; spilling x146 to mem
mov [ rsp + 0x118 ], rdi; spilling x124 to mem
mulx r9, rdi, rbp; x113, x112<- arg1[1] * x19
mov rdx, [ rsi + 0x28 ]; load m64 x11 to register64
mov [ rsp + 0x120 ], r9; spilling x113 to mem
mov r9, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x128 ], rdi; spilling x112 to mem
mov [ rsp + 0x130 ], r8; spilling x142 to mem
mulx rdi, r8, rcx; x105, x104<- arg1[1] * x3
imul rdx, r9, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x138 ], rdi; spilling x105 to mem
mov [ rsp + 0x140 ], r8; spilling x104 to mem
mulx rdi, r8, [ rsi + 0x18 ]; x81, x80<- arg1[3] * x13
mov [ rsp + 0x148 ], rdi; spilling x81 to mem
mov rdi, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x150 ], r8; spilling x80 to mem
mov [ rsp + 0x158 ], r9; spilling x11 to mem
mulx r8, r9, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x160 ], r8; spilling x101 to mem
mov [ rsp + 0x168 ], r9; spilling x100 to mem
mulx r8, r9, rbx; x93, x92<- arg1[2] * x8
mov rdx, [ rsi + 0x20 ]; load m64 x16 to register64
mov [ rsp + 0x170 ], r8; spilling x93 to mem
mulx rdx, r8, [ rsi + 0x20 ]; x69, x68<- arg1[4] * x16
mov [ rsp + 0x178 ], r9; spilling x92 to mem
mov r9, rdx; preserving value of x69 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x180 ], r8; spilling x68 to mem
mov [ rsp + 0x188 ], rdi; spilling x13 to mem
mulx r8, rdi, [ rsp + 0x48 ]; x45, x44<- arg1[5] * x4
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x190 ], r9; spilling x69 to mem
mulx r10, r9, r10; x35, x34<- arg1[6] * x6
mov rdx, rcx; x3 to rdx
mov [ rsp + 0x198 ], r13; spilling x10 to mem
mulx rcx, r13, [ rsi + 0x28 ]; x37, x36<- arg1[5] * x3
add r9, r13; could be done better, if r0 has been u8 as well
adcx rcx, r10
mov r10, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x30 ]; saving x7 in rdx.
mulx rdx, r13, [ rsi + 0x30 ]; x43, x42<- arg1[6] * x7
test al, al
adox r9, r13
adox rdx, rcx
adcx r9, rdi
adcx r8, rdx
add r9, [ rsp + 0x180 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x190 ]
add r9, [ rsp + 0x150 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x148 ]
add r9, [ rsp + 0x178 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x170 ]
xor rdi, rdi
adox r9, [ rsp + 0x168 ]
adox r8, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x140 ]
mov rcx, -0x3 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, [ rsp + 0x128 ]
seto r13b; spill OF x261 to reg (r13)
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, discard the information #workaround). #last resort
adox r9, [ rsp + 0x118 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, rcx, r10; x89, x88<- arg1[2] * x3
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1a0 ], rdi; spilling x89 to mem
mov [ rsp + 0x1a8 ], rcx; spilling x88 to mem
mulx rdi, rcx, r10; x33, x32<- arg1[6] * x3
mov rdx, rbx; x8 to rdx
mov [ rsp + 0x1b0 ], rdi; spilling x33 to mem
mulx rbx, rdi, [ rsi + 0x18 ]; x77, x76<- arg1[3] * x8
adcx r8, [ rsp + 0x138 ]
movzx r13, r13b
lea r8, [ r13 + r8 ]
mov r13, [ rsp + 0x120 ]
lea r8, [r13+r8]
clc;
adcx r9, [ rsp + 0x110 ]
adox r8, [ rsp + 0x108 ]
adc r8, 0x0
add r14, r9; could be done better, if r0 has been u8 as well
adc r8, 0x0
mov r13, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x1b8 ], rbx; spilling x77 to mem
mulx r9, rbx, rax; x123, x122<- arg1[0] * x15
mov rdx, r14; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x337, x336, size: 2
shrd rdx, r8, 56; x336 <- x335||x333 >> 56
mov r8, rdx; preserving value of x336 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x1c0 ], r9; spilling x123 to mem
mov [ rsp + 0x1c8 ], rbx; spilling x122 to mem
mulx r9, rbx, r12; x111, x110<- arg1[1] * x18
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x1d0 ], r8; spilling x336 to mem
mulx rbp, r8, rbp; x99, x98<- arg1[2] * x19
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1d8 ], r9; spilling x111 to mem
mov [ rsp + 0x1e0 ], rbx; spilling x110 to mem
mulx r9, rbx, [ rsp + 0x48 ]; x41, x40<- arg1[6] * x4
add rcx, rbx; could be done better, if r0 has been u8 as well
adcx r9, [ rsp + 0x1b0 ]
mov rdx, [ rsp + 0x188 ]; x13 to rdx
mulx rdx, rbx, [ rsi + 0x20 ]; x65, x64<- arg1[4] * x13
add rcx, rbx; could be done better, if r0 has been u8 as well
adcx rdx, r9
add rcx, rdi; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x1b8 ]
xor rdi, rdi
adox rcx, [ rsp + 0x1a8 ]
adcx rcx, r8
adox rdx, [ rsp + 0x1a0 ]
adcx rbp, rdx
add rcx, [ rsp + 0x1e0 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r8, r9, [ rsp + 0xa0 ]; x31, x30<- arg1[7] * x1
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rax, rbx, rax; x109, x108<- arg1[1] * x15
adcx rbp, [ rsp + 0x1d8 ]
xor rdx, rdx
adox rcx, [ rsp + 0x1c8 ]
adox rbp, [ rsp + 0x1c0 ]
mov [ rsp + 0x1e8 ], r15; spilling x164 to mem
mov r15, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsp + 0x28 ]; saving x2 in rdx.
mov [ rsp + 0x1f0 ], rax; spilling x109 to mem
mulx rdx, rax, [ rsi + 0x38 ]; x39, x38<- arg1[7] * x2
mov r15, rdx; preserving value of x39 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x1f8 ], rbx; spilling x108 to mem
mov [ rsp + 0x200 ], r8; spilling x31 to mem
mulx rbx, r8, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x208 ], rbx; spilling x85 to mem
mulx r12, rbx, r12; x97, x96<- arg1[2] * x18
adcx rcx, [ rsp + 0x1d0 ]
mov rdx, r10; x3 to rdx
mov [ rsp + 0x210 ], r12; spilling x97 to mem
mulx r10, r12, [ rsi + 0x18 ]; x73, x72<- arg1[3] * x3
adc rbp, 0x0
mov [ rsp + 0x218 ], rbx; spilling x96 to mem
mov rbx, rcx; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd rbx, rbp, 56; x349 <- x343||x341 >> 56
add r9, rax; could be done better, if r0 has been u8 as well
adcx r15, [ rsp + 0x200 ]
mov rax, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x220 ], rbx; spilling x349 to mem
mulx rbp, rbx, [ rsp + 0x198 ]; x121, x120<- arg1[0] * x10
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x228 ], rbp; spilling x121 to mem
mulx r13, rbp, r13; x61, x60<- arg1[4] * x8
mov rdx, [ rsp + 0x158 ]; x11 to rdx
mov [ rsp + 0x230 ], rbx; spilling x120 to mem
mulx rdx, rbx, [ rsi + 0x28 ]; x53, x52<- arg1[5] * x11
add r9, rbx; could be done better, if r0 has been u8 as well
adcx rdx, r15
xor r15, r15
adox r9, rbp
adcx r9, r12
adox r13, rdx
adcx r10, r13
add r9, r8; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x208 ]
xor r8, r8
adox r9, [ rsp + 0x218 ]
adcx r9, [ rsp + 0x1f8 ]
adox r10, [ rsp + 0x210 ]
adcx r10, [ rsp + 0x1f0 ]
add r9, [ rsp + 0x230 ]; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x228 ]
imul r15, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
add r9, [ rsp + 0x220 ]; could be done better, if r0 has been u8 as well
adc r10, 0x0
mov r12, 0xffffffffffffff ; moving imm to reg
mov rbp, [ rsp + 0x1e8 ]; x332, copying x164 here, cause x164 is needed in a reg for other than x332, namely all: , x332, size: 1
and rbp, r12; x332 <- x164&0xffffffffffffff
mov rbx, r9; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x359, x360, size: 2
shrd rbx, r10, 56; x359 <- x353||x351 >> 56
mov rdx, [ rsp + 0x38 ]; load m64 x29 to register64
sar byte [ rsp + 0x90 ], 1
adcx rdx, [ rsp + 0x88 ]
lea rbx, [ rbx + rbp ]
mov r13, rbx; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x366, x365, size: 2
shr r13, 56; x365 <- x361>> 56
mov r10, r13; x370, copying x365 here, cause x365 is needed in a reg for other than x370, namely all: , x370, x369, size: 2
add r10, [ rsp + 0xd8 ]
mov rbp, r10; x376, copying x370 here, cause x370 is needed in a reg for other than x376, namely all: , x376, x375, size: 2
and rbp, r12; x376 <- x370&0xffffffffffffff
and r9, r12; x360 <- x351&0xffffffffffffff
sar byte [ rsp + 0x78 ], 1
adcx rdx, [ rsp + 0x40 ]
sar byte [ rsp + 0x68 ], 1
adcx rdx, [ rsp + 0x20 ]
mov r8, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r8 + 0x0 ], rbp; out1[0] = x376
and r14, r12; x337 <- x333&0xffffffffffffff
mov rbp, rdx; preserving value of x314 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x0 ], r8; spilling out1 to mem
mulx r12, r8, [ rsp + 0x98 ]; x75, x74<- arg1[3] * x9
sar byte [ rsp + 0x60 ], 1
adcx rbp, [ rsp + 0x18 ]
sar byte [ rsp + 0x58 ], 1
adcx rbp, [ rsp + 0x10 ]
sar byte [ rsp + 0x80 ], 1
adcx rbp, [ rsp + 0x8 ]
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x30 ], r9; out1[6] = x360
mov r9, rdx; preserving value of out1 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x238 ], r14; spilling x337 to mem
mov [ rsp + 0x240 ], r12; spilling x75 to mem
mulx r14, r12, [ rsp + 0x70 ]; x63, x62<- arg1[4] * x14
mov rdx, r15; x21 to rdx
mulx rdx, r15, [ rsi + 0x0 ]; x131, x130<- arg1[0] * x21
rcr byte [ rsp + 0xd0 ], 1
setc [ rsp + 0xd0 ]; keep flag in mem cause it has deps.
adc rbp, 0x0
shrd r11, rbp, 56; x344 <- x340||x338 >> 56
mov rbp, rdx; preserving value of x131 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x0 ], r9; spilling out1 to mem
mulx rax, r9, rax; x25, x24<- arg1[6] * x3
add r9, r12; could be done better, if r0 has been u8 as well
adcx r14, rax
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, rax, [ rsp + 0x48 ]; x87, x86<- arg1[2] * x4
test al, al
adox r9, r8
adox r14, [ rsp + 0x240 ]
adcx r9, rax
adcx r12, r14
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, rax, [ rsp + 0x98 ]; x59, x58<- arg1[4] * x9
test al, al
adox r9, r15
adcx r9, r11
adox rbp, r12
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mulx r15, r11, [ rsp + 0x50 ]; x51, x50<- arg1[5] * x12
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r14, r12, [ rsp + 0xe0 ]; x129, x128<- arg1[0] * x20
adc rbp, 0x0
mov rdx, r9; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x354, x355, size: 2
shrd rdx, rbp, 56; x354 <- x348||x346 >> 56
mov rbp, rdx; preserving value of x354 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x248 ], r14; spilling x129 to mem
mov [ rsp + 0x250 ], r12; spilling x128 to mem
mulx r14, r12, [ rsp + 0x48 ]; x71, x70<- arg1[3] * x4
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x258 ], rbp; spilling x354 to mem
mov [ rsp + 0x260 ], r14; spilling x71 to mem
mulx rbp, r14, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
mov rdx, [ rsp + 0xa0 ]; x1 to rdx
mov [ rsp + 0x268 ], rbp; spilling x117 to mem
mulx rdx, rbp, [ rsi + 0x38 ]; x23, x22<- arg1[7] * x1
add rbp, r11; could be done better, if r0 has been u8 as well
adcx r15, rdx
test al, al
adox rbp, rax
adox r8, r15
adcx rbp, r12
adcx r8, [ rsp + 0x260 ]
add rbp, r14; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x268 ]
add rbp, [ rsp + 0x250 ]; could be done better, if r0 has been u8 as well
adcx r8, [ rsp + 0x248 ]
add rbp, [ rsp + 0x258 ]; could be done better, if r0 has been u8 as well
adc r8, 0x0
add r13, [ rsp + 0x238 ]
mov rax, 0xffffffffffffff ; moving imm to reg
mov r11, [ rsp + 0x130 ]; x147, copying x142 here, cause x142 is needed in a reg for other than x147, namely all: , x147, size: 1
and r11, rax; x147 <- x142&0xffffffffffffff
and rbx, rax; x366 <- x361&0xffffffffffffff
shr r10, 56; x375 <- x370>> 56
mov r12, rbp; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x363, x362, size: 2
shrd r12, r8, 56; x362 <- x358||x356 >> 56
lea r12, [ r12 + r11 ]
and rbp, rax; x363 <- x356&0xffffffffffffff
mov r14, r12; x368, copying x364 here, cause x364 is needed in a reg for other than x368, namely all: , x368, x367, size: 2
and r14, rax; x368 <- x364&0xffffffffffffff
and rcx, rax; x350 <- x341&0xffffffffffffff
and r9, rax; x355 <- x346&0xffffffffffffff
shr r12, 56; x367 <- x364>> 56
lea r12, [ r12 + r13 ]
lea r10, [ r10 + r9 ]
mov rdx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdx + 0x8 ], r10; out1[1] = x377
mov r15, r12; x373, copying x371 here, cause x371 is needed in a reg for other than x373, namely all: , x372, x373, size: 2
and r15, rax; x373 <- x371&0xffffffffffffff
shr r12, 56; x372 <- x371>> 56
mov [ rdx + 0x20 ], r15; out1[4] = x373
mov [ rdx + 0x18 ], r14; out1[3] = x368
mov [ rdx + 0x38 ], rbx; out1[7] = x366
mov [ rdx + 0x10 ], rbp; out1[2] = x363
lea r12, [ r12 + rcx ]
mov [ rdx + 0x28 ], r12; out1[5] = x374
mov rbx, [ rsp + 0x270 ]; restoring from stack
mov rbp, [ rsp + 0x278 ]; restoring from stack
mov r12, [ rsp + 0x280 ]; restoring from stack
mov r13, [ rsp + 0x288 ]; restoring from stack
mov r14, [ rsp + 0x290 ]; restoring from stack
mov r15, [ rsp + 0x298 ]; restoring from stack
add rsp, 0x2a0 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 101.0025, best 63.58762886597938, lastGood 65.47422680412372
; seed 3824668340341651 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3356083 ms / 60000 runs=> 55.93471666666667ms/run
; Time spent for assembling and measureing (initial batch_size=189, initial num_batches=101): 438243 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.13058169300342096
; number reverted permutation/ tried permutation: 24676 / 30050 =82.116%
; number reverted decision/ tried decision: 24076 / 29951 =80.385%