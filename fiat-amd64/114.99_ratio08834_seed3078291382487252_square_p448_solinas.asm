SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x1e8 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x1b8 ], rbx; saving to stack
mov [ rsp + 0x1c0 ], rbp; saving to stack
mov [ rsp + 0x1c8 ], r12; saving to stack
mov [ rsp + 0x1d0 ], r13; saving to stack
mov [ rsp + 0x1d8 ], r14; saving to stack
mov [ rsp + 0x1e0 ], r15; saving to stack
mov rax, [ rsi + 0x38 ]; load m64 x2 to register64
mov r10, [ rsi + 0x30 ]; load m64 x7 to register64
mov r11, [ rsi + 0x20 ]; load m64 x17 to register64
mov rbx, [ rsi + 0x28 ]; load m64 x12 to register64
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r11, rbp, r11; x67, x66<- arg1[4] * x17
imul r12, rax, 0x2; x4 <- x2 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r13, r14, r12; x103, x102<- arg1[1] * x4
mov r15, [ rsi + 0x38 ]; load m64 x1 to register64
imul rdx, rbx, 0x2; x14 <- x12 * 0x2
mov rcx, [ rsi + 0x30 ]; load m64 x6 to register64
imul r8, r10, 0x2; x9 <- x7 * 0x2
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x18 ]; x79, x78<- arg1[3] * x14
mov [ rsp + 0x8 ], rax; spilling x2 to mem
mov rax, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x10 ], r13; spilling x103 to mem
mov [ rsp + 0x18 ], r9; spilling x79 to mem
mulx r13, r9, r8; x91, x90<- arg1[2] * x9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x20 ], r13; spilling x91 to mem
mov [ rsp + 0x28 ], r11; spilling x67 to mem
mulx r13, r11, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
imul rdx, r15, 0x2; x3 <- x1 * 0x2
mov [ rsp + 0x30 ], r13; spilling x133 to mem
mov [ rsp + 0x38 ], r11; spilling x132 to mem
mulx r13, r11, [ rsi + 0x28 ]; x29, x28<- arg1[5] * x3
xchg rdx, rcx; x6, swapping with x3, which is currently in rdx
mov [ rsp + 0x40 ], r12; spilling x4 to mem
mov [ rsp + 0x48 ], r13; spilling x29 to mem
mulx r12, r13, [ rsi + 0x30 ]; x27, x26<- arg1[6] * x6
mov [ rsp + 0x50 ], r12; spilling x27 to mem
imul r12, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
mov [ rsp + 0x58 ], r12; spilling x18 to mem
xor r12, r12
adox r13, r11
adcx r13, rbp
setc bpl; spill CF x309 to reg (rbp)
seto r11b; spill OF x305 to reg (r11)
imul r12, rdx, 0x2; x8 <- x6 * 0x2
mov [ rsp + 0x60 ], rbx; spilling x12 to mem
imul rbx, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov byte [ rsp + 0x68 ], bpl; spilling byte x309 to mem
imul rbp, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov [ rsp + 0x70 ], r10; spilling x7 to mem
xor r10, r10
adox r13, rdi
adcx r13, r9
setc dil; spill CF x317 to reg (rdi)
seto r9b; spill OF x313 to reg (r9)
imul r10, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
mov byte [ rsp + 0x78 ], dil; spilling byte x317 to mem
mov rdi, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov byte [ rsp + 0x80 ], r9b; spilling byte x313 to mem
mov byte [ rsp + 0x88 ], r11b; spilling byte x305 to mem
mulx r9, r11, rbx; x95, x94<- arg1[2] * x15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x90 ], rax; spilling x14 to mem
mov [ rsp + 0x98 ], r9; spilling x95 to mem
mulx rax, r9, r10; x107, x106<- arg1[1] * x10
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xa0 ], rax; spilling x107 to mem
mov [ rsp + 0xa8 ], r9; spilling x106 to mem
mulx rax, r9, r12; x49, x48<- arg1[5] * x8
test al, al
adox r13, r14
adcx r13, [ rsp + 0x38 ]
mov rdx, rcx; x3 to rdx
mulx rcx, r14, [ rsi + 0x20 ]; x57, x56<- arg1[4] * x3
mov [ rsp + 0xb0 ], r8; spilling x9 to mem
setc r8b; spill CF x325 to reg (r8)
clc;
adcx r9, r14
mov r14, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0xb8 ], r13; spilling x324 to mem
mulx rbp, r13, rbp; x119, x118<- arg1[0] * x5
adcx rcx, rax
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0xc0 ], r15; spilling x1 to mem
mulx rax, r15, [ rsp + 0x58 ]; x83, x82<- arg1[3] * x18
clc;
adcx r9, r15
mov rdx, [ rsp + 0x48 ]; load m64 x29 to register64
movzx r15, byte [ rsp + 0x88 ]; load byte memx305 to register64
lea rdx, [ r15 + rdx ]
mov r15, [ rsp + 0x50 ]
lea rdx, [r15+rdx]
adcx rax, rcx
movzx r15, byte [ rsp + 0x68 ]; load byte memx309 to register64
lea rdx, [ r15 + rdx ]
mov r15, [ rsp + 0x28 ]
lea rdx, [r15+rdx]
movzx r15, byte [ rsp + 0x80 ]; load byte memx313 to register64
lea rdx, [ r15 + rdx ]
mov r15, [ rsp + 0x18 ]
lea rdx, [r15+rdx]
clc;
adcx r9, r11
adcx rax, [ rsp + 0x98 ]
movzx r15, byte [ rsp + 0x78 ]; load byte memx317 to register64
lea rdx, [ r15 + rdx ]
mov r15, [ rsp + 0x20 ]
lea rdx, [r15+rdx]
adox rdx, [ rsp + 0x10 ]
xor r15, r15
adox r9, [ rsp + 0xa8 ]
adox rax, [ rsp + 0xa0 ]
sar  r8b, 1
adcx rdx, [ rsp + 0x30 ]
adox r9, r13
adox rbp, rax
mov r11, r9; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x332, x331, size: 2
shrd r11, rbp, 56; x331 <- x166||x164 >> 56
imul r8, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
mov r13, r11; x338, copying x331 here, cause x331 is needed in a reg for other than x338, namely all: , x333--x334, x338--x339, size: 2
test al, al
adox r13, [ rsp + 0xb8 ]
adox rdx, r15
mov rcx, r13; x344, copying x338 here, cause x338 is needed in a reg for other than x344, namely all: , x345, x344, size: 2
shrd rcx, rdx, 56; x344 <- x340||x338 >> 56
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, rbp, [ rsp + 0x40 ]; x87, x86<- arg1[2] * x4
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xc8 ], rdi; spilling x6 to mem
mulx r15, rdi, [ rsp + 0x90 ]; x63, x62<- arg1[4] * x14
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0xd0 ], rcx; spilling x344 to mem
mov [ rsp + 0xd8 ], rax; spilling x87 to mem
mulx rcx, rax, r14; x25, x24<- arg1[6] * x3
test al, al
adox rax, rdi
adox r15, rcx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rdi, rcx, [ rsp + 0xb0 ]; x75, x74<- arg1[3] * x9
adcx rax, rcx
adcx rdi, r15
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r15, r8; x131, x130<- arg1[0] * x21
mov rdx, [ rsi + 0x28 ]; load m64 x11 to register64
imul rcx, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
add rax, rbp; could be done better, if r0 has been u8 as well
adcx rdi, [ rsp + 0xd8 ]
xor rbp, rbp
adox rax, r15
adcx rax, [ rsp + 0xd0 ]
mov r15, rdx; preserving value of x11 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0xe0 ], rax; spilling x346 to mem
mulx rbp, rax, r14; x105, x104<- arg1[1] * x3
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xe8 ], rbx; spilling x15 to mem
mov [ rsp + 0xf0 ], rbp; spilling x105 to mem
mulx rbx, rbp, [ rsp + 0x40 ]; x55, x54<- arg1[4] * x4
adox r8, rdi
adc r8, 0x0
imul rdx, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov [ rsp + 0xf8 ], r8; spilling x348 to mem
mulx rdi, r8, [ rsi + 0x8 ]; x115, x114<- arg1[1] * x20
mov [ rsp + 0x100 ], r10; spilling x10 to mem
mov r10, 0xffffffffffffff ; moving imm to reg
and r13, r10; x345 <- x338&0xffffffffffffff
mov r10, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x108 ], r13; spilling x345 to mem
mov [ rsp + 0x110 ], rax; spilling x104 to mem
mulx r13, rax, [ rsp + 0xb0 ]; x47, x46<- arg1[5] * x9
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x118 ], r12; spilling x8 to mem
mov [ rsp + 0x120 ], r15; spilling x11 to mem
mulx r12, r15, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
adox rax, rbp
adox rbx, r13
mov rdx, rcx; x19 to rdx
mulx rcx, rbp, [ rsi + 0x8 ]; x113, x112<- arg1[1] * x19
mov [ rsp + 0x128 ], rcx; spilling x113 to mem
mulx r13, rcx, [ rsi + 0x0 ]; x127, x126<- arg1[0] * x19
adcx rax, r8
mov r8, [ rsi + 0x20 ]; load m64 x16 to register64
adcx rdi, rbx
add rax, rcx; could be done better, if r0 has been u8 as well
adcx r13, rdi
mov rbx, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, rdi, [ rsp + 0x58 ]; x125, x124<- arg1[0] * x18
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x130 ], rcx; spilling x125 to mem
mov [ rsp + 0x138 ], rdi; spilling x124 to mem
mulx rcx, rdi, [ rsp + 0x40 ]; x45, x44<- arg1[5] * x4
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x140 ], rbp; spilling x112 to mem
mov [ rsp + 0x148 ], r12; spilling x101 to mem
mulx rbp, r12, [ rsp + 0xc8 ]; x35, x34<- arg1[6] * x6
imul rdx, [ rsp + 0x120 ], 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x150 ], r15; spilling x100 to mem
mov r15, rax; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd r15, r13, 56; x146 <- x144||x142 >> 56
mov r13, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x158 ], r15; spilling x146 to mem
mov [ rsp + 0x160 ], rcx; spilling x45 to mem
mulx r15, rcx, r14; x37, x36<- arg1[5] * x3
mov rdx, r8; x16 to rdx
mulx rdx, r8, [ rsi + 0x20 ]; x69, x68<- arg1[4] * x16
add r12, rcx; could be done better, if r0 has been u8 as well
adcx r15, rbp
mov rbp, rdx; preserving value of x69 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x168 ], r8; spilling x68 to mem
mulx rcx, r8, [ rsp + 0x118 ]; x93, x92<- arg1[2] * x8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x170 ], rcx; spilling x93 to mem
mov [ rsp + 0x178 ], r8; spilling x92 to mem
mulx rcx, r8, r13; x81, x80<- arg1[3] * x13
mov rdx, [ rsp + 0x70 ]; x7 to rdx
mov [ rsp + 0x180 ], rcx; spilling x81 to mem
mulx rdx, rcx, [ rsi + 0x30 ]; x43, x42<- arg1[6] * x7
add r12, rcx; could be done better, if r0 has been u8 as well
adcx rdx, r15
xor r15, r15
adox r12, rdi
adox rdx, [ rsp + 0x160 ]
adcx r12, [ rsp + 0x168 ]
adcx rbp, rdx
xor rdi, rdi
adox r12, r8
adcx r12, [ rsp + 0x178 ]
adox rbp, [ rsp + 0x180 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, r15, rbx; x99, x98<- arg1[2] * x19
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, [ rsp + 0x150 ]
adcx rbp, [ rsp + 0x170 ]
adox rbp, [ rsp + 0x148 ]
add r12, [ rsp + 0x110 ]; could be done better, if r0 has been u8 as well
adcx rbp, [ rsp + 0xf0 ]
add r12, [ rsp + 0x140 ]; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r8, rcx, [ rsp + 0x40 ]; x41, x40<- arg1[6] * x4
adcx rbp, [ rsp + 0x128 ]
mov rdx, r14; x3 to rdx
mulx r14, rdi, [ rsi + 0x10 ]; x89, x88<- arg1[2] * x3
mov [ rsp + 0x188 ], rbx; spilling x99 to mem
xor rbx, rbx
adox r12, [ rsp + 0x138 ]
adox rbp, [ rsp + 0x130 ]
adcx r12, [ rsp + 0x158 ]
adc rbp, 0x0
mov [ rsp + 0x190 ], r14; spilling x89 to mem
xor r14, r14
adox r11, r12
adox rbp, r14
mulx rbx, r12, [ rsi + 0x30 ]; x33, x32<- arg1[6] * x3
mov r14, r11; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x337, x336, size: 2
shrd r14, rbp, 56; x336 <- x335||x333 >> 56
xor rbp, rbp
adox r12, rcx
adox r8, rbx
mov rcx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r13, rbx, r13; x65, x64<- arg1[4] * x13
adcx r12, rbx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, rbp, [ rsp + 0x118 ]; x77, x76<- arg1[3] * x8
adcx r13, r8
add r12, rbp; could be done better, if r0 has been u8 as well
adcx rbx, r13
test al, al
adox r12, rdi
adcx r12, r15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rdi, [ rsp + 0x58 ]; x111, x110<- arg1[1] * x18
adox rbx, [ rsp + 0x190 ]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, rdi
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rbp, [ rsp + 0xe8 ]; x123, x122<- arg1[0] * x15
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r13, rdi, [ rsp + 0x100 ]; x121, x120<- arg1[0] * x10
adcx rbx, [ rsp + 0x188 ]
adox r15, rbx
xor rdx, rdx
adox r12, rbp
adcx r12, r14
mov r14, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, rbx, [ rsp + 0xe8 ]; x109, x108<- arg1[1] * x15
adox r8, r15
adc r8, 0x0
mov rdx, r12; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd rdx, r8, 56; x349 <- x343||x341 >> 56
mov r15, rdx; preserving value of x349 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx r8, r14, [ rsp + 0xc0 ]; x31, x30<- arg1[7] * x1
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x198 ], r15; spilling x349 to mem
mov [ rsp + 0x1a0 ], r13; spilling x121 to mem
mulx r15, r13, [ rsp + 0x120 ]; x53, x52<- arg1[5] * x11
mov rdx, [ rsp + 0x8 ]; x2 to rdx
mov [ rsp + 0x1a8 ], rdi; spilling x120 to mem
mulx rdx, rdi, [ rsi + 0x38 ]; x39, x38<- arg1[7] * x2
test al, al
adox r14, rdi
adox rdx, r8
adcx r14, r13
adcx r15, rdx
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r8, r13, [ rsp + 0x118 ]; x61, x60<- arg1[4] * x8
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rcx, rdi, rcx; x73, x72<- arg1[3] * x3
test al, al
adox r14, r13
adcx r14, rdi
adox r8, r15
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r13, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
adcx rcx, r8
test al, al
adox r14, r13
mov rdx, [ rsp + 0x58 ]; x18 to rdx
mulx rdx, rdi, [ rsi + 0x10 ]; x97, x96<- arg1[2] * x18
adox r15, rcx
adcx r14, rdi
adcx rdx, r15
add r14, rbx; could be done better, if r0 has been u8 as well
adcx rbp, rdx
mov rbx, 0xffffffffffffff ; moving imm to reg
and r9, rbx; x332 <- x164&0xffffffffffffff
adox r14, [ rsp + 0x1a8 ]
adox rbp, [ rsp + 0x1a0 ]
mov rdx, [ rsp + 0xb0 ]; x9 to rdx
mulx rdx, r8, [ rsi + 0x20 ]; x59, x58<- arg1[4] * x9
adcx r14, [ rsp + 0x198 ]
adc rbp, 0x0
mov r13, r14; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x360, x359, size: 2
shrd r13, rbp, 56; x359 <- x353||x351 >> 56
lea r13, [ r13 + r9 ]
mov rcx, r13; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, x366, size: 2
shr rcx, 56; x365 <- x361>> 56
mov rdi, [ rsp + 0xe0 ]; load m64 x346 to register64
mov r15, [ rsp + 0xf8 ]; load m64 x348 to register64
mov r9, rdi; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x355, x354, size: 2
shrd r9, r15, 56; x354 <- x348||x346 >> 56
and r11, rbx; x337 <- x333&0xffffffffffffff
mov r15, rcx; x370, copying x365 here, cause x365 is needed in a reg for other than x370, namely all: , x370, x369, size: 2
add r15, [ rsp + 0x108 ]
lea r11, [ r11 + rcx ]
mov rbp, r15; x375, copying x370 here, cause x370 is needed in a reg for other than x375, namely all: , x375, x376, size: 2
shr rbp, 56; x375 <- x370>> 56
and rax, rbx; x147 <- x142&0xffffffffffffff
and rdi, rbx; x355 <- x346&0xffffffffffffff
lea rbp, [ rbp + rdi ]
mov rcx, rdx; preserving value of x59 into a new reg
mov rdx, [ rsp + 0xc0 ]; saving x1 in rdx.
mulx rdx, rdi, [ rsi + 0x38 ]; x23, x22<- arg1[7] * x1
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbx + 0x8 ], rbp; out1[1] = x377
mov rbp, rdx; preserving value of x23 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x0 ], rbx; spilling out1 to mem
mov [ rsp + 0x1b0 ], r11; spilling x369 to mem
mulx rbx, r11, [ rsp + 0x60 ]; x51, x50<- arg1[5] * x12
adox rdi, r11
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, r10; x129, x128<- arg1[0] * x20
adox rbx, rbp
adcx rdi, r8
adcx rcx, rbx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rbp, [ rsp + 0x40 ]; x71, x70<- arg1[3] * x4
test al, al
adox rdi, rbp
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
adox r8, rcx
adcx rdi, rbp
adcx rbx, r8
test al, al
adox rdi, r11
adox r10, rbx
adcx rdi, r9
adc r10, 0x0
mov rdx, rdi; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x362, x363, size: 2
shrd rdx, r10, 56; x362 <- x358||x356 >> 56
mov r9, 0xffffffffffffff ; moving imm to reg
and r13, r9; x366 <- x361&0xffffffffffffff
and r12, r9; x350 <- x341&0xffffffffffffff
lea rdx, [ rdx + rax ]
mov rax, rdx; x367, copying x364 here, cause x364 is needed in a reg for other than x367, namely all: , x368, x367, size: 2
shr rax, 56; x367 <- x364>> 56
add rax, [ rsp + 0x1b0 ]
mov r11, rax; x372, copying x371 here, cause x371 is needed in a reg for other than x372, namely all: , x372, x373, size: 2
shr r11, 56; x372 <- x371>> 56
and rdx, r9; x368 <- x364&0xffffffffffffff
and r14, r9; x360 <- x351&0xffffffffffffff
lea r11, [ r11 + r12 ]
and rdi, r9; x363 <- x356&0xffffffffffffff
mov rcx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rcx + 0x30 ], r14; out1[6] = x360
mov [ rcx + 0x18 ], rdx; out1[3] = x368
and rax, r9; x373 <- x371&0xffffffffffffff
mov [ rcx + 0x10 ], rdi; out1[2] = x363
and r15, r9; x376 <- x370&0xffffffffffffff
mov [ rcx + 0x28 ], r11; out1[5] = x374
mov [ rcx + 0x20 ], rax; out1[4] = x373
mov [ rcx + 0x38 ], r13; out1[7] = x366
mov [ rcx + 0x0 ], r15; out1[0] = x376
mov rbx, [ rsp + 0x1b8 ]; restoring from stack
mov rbp, [ rsp + 0x1c0 ]; restoring from stack
mov r12, [ rsp + 0x1c8 ]; restoring from stack
mov r13, [ rsp + 0x1d0 ]; restoring from stack
mov r14, [ rsp + 0x1d8 ]; restoring from stack
mov r15, [ rsp + 0x1e0 ]; restoring from stack
add rsp, 0x1e8 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4664 MHz
; first cyclecount 170.12, best 113.03092783505154, lastGood 114.98989898989899
; seed 3078291382487252 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2145940 ms / 60000 runs=> 35.76566666666667ms/run
; Time spent for assembling and measureing (initial batch_size=97, initial num_batches=101): 133546 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.06223193565523733
; number reverted permutation/ tried permutation: 22067 / 29832 =73.971%
; number reverted decision/ tried decision: 22772 / 30169 =75.481%