SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x2c0 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x290 ], rbx; saving to stack
mov [ rsp + 0x298 ], rbp; saving to stack
mov [ rsp + 0x2a0 ], r12; saving to stack
mov [ rsp + 0x2a8 ], r13; saving to stack
mov [ rsp + 0x2b0 ], r14; saving to stack
mov [ rsp + 0x2b8 ], r15; saving to stack
imul rax, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
mov r10, [ rsi + 0x38 ]; load m64 x2 to register64
mov r11, [ rsi + 0x30 ]; load m64 x7 to register64
imul rbx, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r12, rbx; x115, x114<- arg1[1] * x20
imul r13, r10, 0x2; x4 <- x2 * 0x2
imul r14, r11, 0x2; x9 <- x7 * 0x2
mov rdx, r14; x9 to rdx
mulx r14, r15, [ rsi + 0x28 ]; x47, x46<- arg1[5] * x9
mov rcx, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, r9, rax; x127, x126<- arg1[0] * x19
mov rdx, r13; x4 to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r13, rdi, [ rsi + 0x20 ]; x55, x54<- arg1[4] * x4
mov [ rsp + 0x8 ], r8; spilling x127 to mem
mov r8, [ rsi + 0x30 ]; load m64 x6 to register64
test al, al
adox r15, rdi
xchg rdx, rax; x19, swapping with x4, which is currently in rdx
mov [ rsp + 0x10 ], r8; spilling x6 to mem
mulx rdi, r8, [ rsi + 0x8 ]; x113, x112<- arg1[1] * x19
adox r13, r14
mov r14, [ rsi + 0x20 ]; load m64 x16 to register64
adcx r15, r12
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r9
adcx rbp, r13
mov r9, [ rsi + 0x28 ]; load m64 x11 to register64
adox rbp, [ rsp + 0x8 ]
mov r13, [ rsi + 0x38 ]; load m64 x1 to register64
imul r12, [ rsp + 0x10 ], 0x2; x8 <- x6 * 0x2
mov [ rsp + 0x18 ], rbx; spilling x20 to mem
mov rbx, r15; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd rbx, rbp, 56; x146 <- x144||x142 >> 56
mov rbp, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x20 ], rcx; spilling x9 to mem
mov [ rsp + 0x28 ], r10; spilling x2 to mem
mulx rcx, r10, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
imul rdx, r13, 0x2; x3 <- x1 * 0x2
mov [ rsp + 0x30 ], rdi; spilling x113 to mem
mov [ rsp + 0x38 ], rcx; spilling x101 to mem
mulx rdi, rcx, [ rsi + 0x28 ]; x37, x36<- arg1[5] * x3
mov [ rsp + 0x40 ], rdi; spilling x37 to mem
imul rdi, r9, 0x2; x13 <- x11 * 0x2
mov [ rsp + 0x48 ], rbx; spilling x146 to mem
mov rbx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x10 ]; saving x6 in rdx.
mov [ rsp + 0x50 ], r8; spilling x112 to mem
mov [ rsp + 0x58 ], r10; spilling x100 to mem
mulx r8, r10, [ rsi + 0x30 ]; x35, x34<- arg1[6] * x6
xchg rdx, r14; x16, swapping with x6, which is currently in rdx
mov [ rsp + 0x60 ], r8; spilling x35 to mem
mulx rdx, r8, [ rsi + 0x20 ]; x69, x68<- arg1[4] * x16
mov [ rsp + 0x68 ], r8; spilling x68 to mem
mov r8, rdx; preserving value of x69 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x70 ], rdi; spilling x13 to mem
mov [ rsp + 0x78 ], r12; spilling x8 to mem
mulx rdi, r12, rax; x45, x44<- arg1[5] * x4
mov rdx, r11; x7 to rdx
mulx rdx, r11, [ rsi + 0x30 ]; x43, x42<- arg1[6] * x7
mov [ rsp + 0x80 ], r8; spilling x69 to mem
imul r8, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
test al, al
adox r10, rcx
mov rcx, rdx; preserving value of x43 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x88 ], rdi; spilling x45 to mem
mov [ rsp + 0x90 ], r8; spilling x5 to mem
mulx rdi, r8, [ rsp + 0x78 ]; x93, x92<- arg1[2] * x8
seto dl; spill OF x229 to reg (rdx)
mov [ rsp + 0x98 ], rdi; spilling x93 to mem
imul rdi, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
xchg rdx, rdi; x18, swapping with x229, which is currently in rdx
mov [ rsp + 0xa0 ], rbp; spilling x19 to mem
mov [ rsp + 0xa8 ], rcx; spilling x43 to mem
mulx rbp, rcx, [ rsi + 0x0 ]; x125, x124<- arg1[0] * x18
mov [ rsp + 0xb0 ], rbp; spilling x125 to mem
mov rbp, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov byte [ rsp + 0xb8 ], dil; spilling byte x229 to mem
mov [ rsp + 0xc0 ], rcx; spilling x124 to mem
mulx rdi, rcx, [ rsp + 0x70 ]; x81, x80<- arg1[3] * x13
test al, al
adox r10, r11
adcx r10, r12
setc dl; spill CF x237 to reg (rdx)
clc;
adcx r10, [ rsp + 0x68 ]
xchg rdx, rbx; x3, swapping with x237, which is currently in rdx
mulx r12, r11, [ rsi + 0x8 ]; x105, x104<- arg1[1] * x3
mov [ rsp + 0xc8 ], r12; spilling x105 to mem
mov r12, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0xd0 ], rdi; spilling x81 to mem
mov byte [ rsp + 0xd8 ], bl; spilling byte x237 to mem
mulx rdi, rbx, [ rsp + 0x78 ]; x49, x48<- arg1[5] * x8
seto dl; spill OF x233 to reg (rdx)
mov [ rsp + 0xe0 ], rdi; spilling x49 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rcx
setc cl; spill CF x241 to reg (rcx)
seto dil; spill OF x245 to reg (rdi)
mov byte [ rsp + 0xe8 ], dl; spilling byte x233 to mem
imul rdx, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
xchg rdx, r12; x3, swapping with x10, which is currently in rdx
mov byte [ rsp + 0xf0 ], dil; spilling byte x245 to mem
mov byte [ rsp + 0xf8 ], cl; spilling byte x241 to mem
mulx rdi, rcx, [ rsi + 0x20 ]; x57, x56<- arg1[4] * x3
mov [ rsp + 0x100 ], r12; spilling x10 to mem
mov r12, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x90 ]; saving x5 in rdx.
mov [ rsp + 0x108 ], rdi; spilling x57 to mem
mulx rdx, rdi, [ rsi + 0x0 ]; x119, x118<- arg1[0] * x5
mov [ rsp + 0x110 ], rdx; spilling x119 to mem
xor rdx, rdx
adox r10, r8
adcx r10, [ rsp + 0x58 ]
setc r8b; spill CF x253 to reg (r8)
clc;
adcx r10, r11
setc r11b; spill CF x257 to reg (r11)
clc;
adcx r10, [ rsp + 0x50 ]
mov byte [ rsp + 0x118 ], r11b; spilling byte x257 to mem
seto r11b; spill OF x249 to reg (r11)
mov byte [ rsp + 0x120 ], r8b; spilling byte x253 to mem
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, [ rsp + 0xc0 ]
setc dl; spill CF x261 to reg (rdx)
seto r8b; spill OF x265 to reg (r8)
mov byte [ rsp + 0x128 ], r11b; spilling byte x249 to mem
imul r11, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
mov byte [ rsp + 0x130 ], r8b; spilling byte x265 to mem
mov r8b, dl; preserving value of x261 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x138 ], rdi; spilling x118 to mem
mov [ rsp + 0x140 ], rbx; spilling x48 to mem
mulx rdi, rbx, r11; x95, x94<- arg1[2] * x15
xor rdx, rdx
adox r10, [ rsp + 0x48 ]
xchg rdx, rbp; x18, swapping with 0x0, which is currently in rdx
mov byte [ rsp + 0x148 ], r8b; spilling byte x261 to mem
mulx rbp, r8, [ rsi + 0x18 ]; x83, x82<- arg1[3] * x18
adcx rcx, [ rsp + 0x140 ]
mov [ rsp + 0x150 ], r10; spilling x328 to mem
mov r10, [ rsp + 0xe0 ]; load m64 x49 to register64
adcx r10, [ rsp + 0x108 ]
clc;
adcx rcx, r8
adcx rbp, r10
mov r8, rdx; preserving value of x18 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x158 ], r15; spilling x142 to mem
mulx r10, r15, [ rsp + 0x100 ]; x107, x106<- arg1[1] * x10
clc;
adcx rcx, rbx
mov rdx, [ rsp + 0x40 ]; load m64 x37 to register64
movzx rbx, byte [ rsp + 0xb8 ]; load byte memx229 to register64
lea rdx, [ rbx + rdx ]
mov rbx, [ rsp + 0x60 ]
lea rdx, [rbx+rdx]
adcx rdi, rbp
clc;
adcx rcx, r15
movzx rbx, byte [ rsp + 0xe8 ]; load byte memx233 to register64
lea rdx, [ rbx + rdx ]
mov rbx, [ rsp + 0xa8 ]
lea rdx, [rbx+rdx]
movzx rbx, byte [ rsp + 0xd8 ]; load byte memx237 to register64
lea rdx, [ rbx + rdx ]
mov rbx, [ rsp + 0x88 ]
lea rdx, [rbx+rdx]
adcx r10, rdi
clc;
adcx rcx, [ rsp + 0x138 ]
adcx r10, [ rsp + 0x110 ]
movzx rbx, byte [ rsp + 0xf8 ]; load byte memx241 to register64
lea rdx, [ rbx + rdx ]
mov rbx, [ rsp + 0x80 ]
lea rdx, [rbx+rdx]
xchg rdx, r8; x18, swapping with x242, which is currently in rdx
mulx rbx, rbp, [ rsi + 0x8 ]; x111, x110<- arg1[1] * x18
seto r15b; spill OF x329 to reg (r15)
mov rdi, rcx; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x332, x331, size: 2
shrd rdi, r10, 56; x331 <- x166||x164 >> 56
sar byte [ rsp + 0xf0 ], 1
adcx r8, [ rsp + 0xd0 ]
xchg rdx, rax; x4, swapping with x18, which is currently in rdx
mov [ rsp + 0x160 ], r9; spilling x11 to mem
mulx r10, r9, [ rsi + 0x30 ]; x41, x40<- arg1[6] * x4
mov [ rsp + 0x10 ], r14; spilling x6 to mem
mov r14, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x168 ], r13; spilling x1 to mem
mov [ rsp + 0x170 ], rbx; spilling x111 to mem
mulx r13, rbx, r12; x33, x32<- arg1[6] * x3
mov rdx, [ rsp + 0xa0 ]; x19 to rdx
mov [ rsp + 0x178 ], rbp; spilling x110 to mem
mulx rdx, rbp, [ rsi + 0x10 ]; x99, x98<- arg1[2] * x19
sar byte [ rsp + 0x128 ], 1
adcx r8, [ rsp + 0x98 ]
mov [ rsp + 0x180 ], rdx; spilling x99 to mem
mov rdx, rdi; x333, copying x331 here, cause x331 is needed in a reg for other than x333, namely all: , x338--x339, x333--x334, size: 2
adox rdx, [ rsp + 0x150 ]
xchg rdx, r12; x3, swapping with x333, which is currently in rdx
mov [ rsp + 0x188 ], rbp; spilling x98 to mem
mov [ rsp + 0x190 ], r12; spilling x333 to mem
mulx rbp, r12, [ rsi + 0x10 ]; x89, x88<- arg1[2] * x3
mov [ rsp + 0x198 ], rbp; spilling x89 to mem
movzx rbp, byte [ rsp + 0x120 ]; load byte memx253 to register64
lea r8, [ rbp + r8 ]
mov rbp, [ rsp + 0x38 ]
lea r8, [rbp+r8]
movzx rbp, byte [ rsp + 0x118 ]; load byte memx257 to register64
lea r8, [ rbp + r8 ]
mov rbp, [ rsp + 0xc8 ]
lea r8, [rbp+r8]
movzx rbp, byte [ rsp + 0x148 ]; load byte memx261 to register64
lea r8, [ rbp + r8 ]
mov rbp, [ rsp + 0x30 ]
lea r8, [rbp+r8]
xchg rdx, r11; x15, swapping with x3, which is currently in rdx
mov [ rsp + 0x1a0 ], r12; spilling x88 to mem
mulx rbp, r12, [ rsi + 0x0 ]; x123, x122<- arg1[0] * x15
clc;
adcx rbx, r9
mov r9, rdx; preserving value of x15 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x1a8 ], rbp; spilling x123 to mem
mov [ rsp + 0x1b0 ], r12; spilling x122 to mem
mulx rbp, r12, [ rsp + 0x70 ]; x65, x64<- arg1[4] * x13
adcx r10, r13
movzx rdx, byte [ rsp + 0x130 ]; load byte memx265 to register64
lea r8, [ rdx + r8 ]
mov rdx, [ rsp + 0xb0 ]
lea r8, [rdx+r8]
clc;
adcx rbx, r12
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r13, rax; x97, x96<- arg1[2] * x18
movzx rdx, r15b; x330, copying x329 here, cause x329 is needed in a reg for other than x330, namely all: , x330, size: 1
lea rdx, [ rdx + r8 ]
adcx rbp, r10
mov r15, rdx; preserving value of x330 into a new reg
mov rdx, [ rsp + 0x78 ]; saving x8 in rdx.
mulx r12, r10, [ rsi + 0x18 ]; x77, x76<- arg1[3] * x8
clc;
adcx rbx, r10
mov r8, 0x0 ; moving imm to reg
adox r15, r8
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbx, [ rsp + 0x1a0 ]
adcx r12, rbp
mov rbp, [ rsp + 0x190 ]; load m64 x333 to register64
seto r8b; spill OF x213 to reg (r8)
mov r10, rbp; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x336, x337, size: 2
shrd r10, r15, 56; x336 <- x335||x333 >> 56
sar  r8b, 1
adcx r12, [ rsp + 0x198 ]
mov r15, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x1b8 ], rax; spilling x97 to mem
mulx r8, rax, [ rsp + 0x100 ]; x121, x120<- arg1[0] * x10
adox rbx, [ rsp + 0x188 ]
adox r12, [ rsp + 0x180 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x1c0 ], r8; spilling x121 to mem
mov [ rsp + 0x1c8 ], rax; spilling x120 to mem
mulx r8, rax, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
add rbx, [ rsp + 0x178 ]; could be done better, if r0 has been u8 as well
adcx r12, [ rsp + 0x170 ]
add rbx, [ rsp + 0x1b0 ]; could be done better, if r0 has been u8 as well
adcx r12, [ rsp + 0x1a8 ]
xor rdx, rdx
adox rbx, r10
adox r12, rdx
mov r10, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x1d0 ], r13; spilling x96 to mem
mov [ rsp + 0x1d8 ], r8; spilling x85 to mem
mulx r13, r8, [ rsp + 0x168 ]; x31, x30<- arg1[7] * x1
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1e0 ], rax; spilling x84 to mem
mulx r10, rax, [ rsp + 0x28 ]; x39, x38<- arg1[7] * x2
mov rdx, rbx; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd rdx, r12, 56; x349 <- x343||x341 >> 56
add r8, rax; could be done better, if r0 has been u8 as well
mov r12, rdx; preserving value of x349 into a new reg
mov rdx, [ rsp + 0x160 ]; saving x11 in rdx.
mulx rdx, rax, [ rsi + 0x28 ]; x53, x52<- arg1[5] * x11
adcx r10, r13
mov r13, [ rsi + 0x28 ]; load m64 x12 to register64
add r8, rax; could be done better, if r0 has been u8 as well
mov rax, rdx; preserving value of x53 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x1e8 ], r13; spilling x12 to mem
mov [ rsp + 0x1f0 ], r12; spilling x349 to mem
mulx r13, r12, r11; x73, x72<- arg1[3] * x3
mov rdx, r15; x8 to rdx
mulx rdx, r15, [ rsi + 0x20 ]; x61, x60<- arg1[4] * x8
adcx rax, r10
test al, al
adox r8, r15
adox rdx, rax
xchg rdx, r9; x15, swapping with x178, which is currently in rdx
mulx rdx, r10, [ rsi + 0x8 ]; x109, x108<- arg1[1] * x15
adcx r8, r12
adcx r13, r9
mov r12, rdx; preserving value of x109 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r15, rax, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
add r8, [ rsp + 0x1e0 ]; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x1d8 ]
add r8, [ rsp + 0x1d0 ]; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x1b8 ]
mov rdx, 0xffffffffffffff ; moving imm to reg
and rcx, rdx; x332 <- x164&0xffffffffffffff
adox r8, r10
adox r12, r13
xchg rdx, r11; x3, swapping with 0xffffffffffffff, which is currently in rdx
mulx r9, r10, [ rsi + 0x28 ]; x29, x28<- arg1[5] * x3
adcx r8, [ rsp + 0x1c8 ]
adcx r12, [ rsp + 0x1c0 ]
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x1f8 ], r15; spilling x133 to mem
mulx r11, r15, [ rsp + 0x10 ]; x27, x26<- arg1[6] * x6
add r8, [ rsp + 0x1f0 ]; could be done better, if r0 has been u8 as well
adc r12, 0x0
imul rdx, [ rsp + 0x1e8 ], 0x2; x14 <- x12 * 0x2
mov [ rsp + 0x200 ], rax; spilling x132 to mem
mov [ rsp + 0x208 ], rcx; spilling x332 to mem
mulx rax, rcx, [ rsi + 0x18 ]; x79, x78<- arg1[3] * x14
mov [ rsp + 0x210 ], rax; spilling x79 to mem
mov rax, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x218 ], rcx; spilling x78 to mem
mov [ rsp + 0x220 ], r11; spilling x27 to mem
mulx rcx, r11, r14; x103, x102<- arg1[1] * x4
mov rdx, rax; x14 to rdx
mulx rdx, rax, [ rsi + 0x20 ]; x63, x62<- arg1[4] * x14
mov [ rsp + 0x228 ], rdx; spilling x63 to mem
mov rdx, r8; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x359, x360, size: 2
shrd rdx, r12, 56; x359 <- x353||x351 >> 56
add r15, r10; could be done better, if r0 has been u8 as well
mov r10, [ rsi + 0x20 ]; load m64 x17 to register64
xchg rdx, r10; x17, swapping with x359, which is currently in rdx
mulx rdx, r12, [ rsi + 0x20 ]; x67, x66<- arg1[4] * x17
adcx r9, [ rsp + 0x220 ]
add r10, [ rsp + 0x208 ]
mov [ rsp + 0x230 ], rax; spilling x62 to mem
xor rax, rax
adox r15, r12
mov r12, rdx; preserving value of x67 into a new reg
mov rdx, [ rsp + 0x20 ]; saving x9 in rdx.
mov [ rsp + 0x238 ], rcx; spilling x103 to mem
mulx rax, rcx, [ rsi + 0x18 ]; x75, x74<- arg1[3] * x9
adox r12, r9
mov r9, 0xffffffffffffff ; moving imm to reg
mov [ rsp + 0x240 ], rax; spilling x75 to mem
mov rax, r10; x366, copying x361 here, cause x361 is needed in a reg for other than x366, namely all: , x366, x365, size: 2
and rax, r9; x366 <- x361&0xffffffffffffff
xchg rdx, r14; x4, swapping with x9, which is currently in rdx
mov [ rsp + 0x248 ], rax; spilling x366 to mem
mulx r9, rax, [ rsi + 0x10 ]; x87, x86<- arg1[2] * x4
adox r15, [ rsp + 0x218 ]
xchg rdx, r14; x9, swapping with x4, which is currently in rdx
mov [ rsp + 0x250 ], r9; spilling x87 to mem
mov [ rsp + 0x258 ], rax; spilling x86 to mem
mulx r9, rax, [ rsi + 0x10 ]; x91, x90<- arg1[2] * x9
adcx r15, rax
adox r12, [ rsp + 0x210 ]
adcx r9, r12
mulx rdx, rax, [ rsi + 0x20 ]; x59, x58<- arg1[4] * x9
imul r12, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
add r15, r11; could be done better, if r0 has been u8 as well
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x200 ]
mov r11, rdx; preserving value of x59 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x260 ], rax; spilling x58 to mem
mulx r12, rax, r12; x131, x130<- arg1[0] * x21
adcx r9, [ rsp + 0x238 ]
clc;
adcx rdi, r15
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r13, r15, r13; x25, x24<- arg1[6] * x3
adox r9, [ rsp + 0x1f8 ]
adc r9, 0x0
add r15, [ rsp + 0x230 ]; could be done better, if r0 has been u8 as well
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rcx
adcx r13, [ rsp + 0x228 ]
adox r13, [ rsp + 0x240 ]
mov rdx, [ rsp + 0x168 ]; x1 to rdx
mulx rdx, rcx, [ rsi + 0x38 ]; x23, x22<- arg1[7] * x1
shr r10, 56; x365 <- x361>> 56
mov [ rsp + 0x268 ], r11; spilling x59 to mem
xor r11, r11
adox r15, [ rsp + 0x258 ]
adox r13, [ rsp + 0x250 ]
mov r11, rdx; preserving value of x23 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x270 ], rcx; spilling x22 to mem
mov [ rsp + 0x278 ], r10; spilling x365 to mem
mulx rcx, r10, [ rsp + 0x18 ]; x129, x128<- arg1[0] * x20
mov rdx, rdi; x344, copying x338 here, cause x338 is needed in a reg for other than x344, namely all: , x344, x345, size: 2
shrd rdx, r9, 56; x344 <- x340||x338 >> 56
xor r9, r9
adox r15, rax
adcx r15, rdx
mov rdx, r14; x4 to rdx
mulx rdx, r14, [ rsi + 0x18 ]; x71, x70<- arg1[3] * x4
mov rax, rdx; preserving value of x71 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x280 ], rcx; spilling x129 to mem
mulx r9, rcx, [ rsp + 0x1e8 ]; x51, x50<- arg1[5] * x12
adox r12, r13
mov rdx, 0xffffffffffffff ; moving imm to reg
setc r13b; spill CF x347 to reg (r13)
and rdi, rdx; x345 <- x338&0xffffffffffffff
mov [ rsp + 0x288 ], r10; spilling x128 to mem
mov r10, r15; x355, copying x346 here, cause x346 is needed in a reg for other than x355, namely all: , x355, x354, size: 2
and r10, rdx; x355 <- x346&0xffffffffffffff
movzx rdx, r13b; x348, copying x347 here, cause x347 is needed in a reg for other than x348, namely all: , x348, size: 1
lea rdx, [ rdx + r12 ]
add rdi, [ rsp + 0x278 ]
mov r13, rdi; x375, copying x370 here, cause x370 is needed in a reg for other than x375, namely all: , x376, x375, size: 2
shr r13, 56; x375 <- x370>> 56
add rcx, [ rsp + 0x270 ]; could be done better, if r0 has been u8 as well
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x260 ]
lea r13, [ r13 + r10 ]
adcx r9, r11
mov r11, rdx; preserving value of x348 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r10, r12, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
adox r9, [ rsp + 0x268 ]
test al, al
adox rcx, r14
adcx rcx, r12
adox rax, r9
adcx r10, rax
shrd r15, r11, 56; x354 <- x348||x346 >> 56
xor rdx, rdx
adox rcx, [ rsp + 0x288 ]
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x8 ], r13; out1[1] = x377
adox r10, [ rsp + 0x280 ]
mov r11, 0xffffffffffffff ; moving imm to reg
mov r12, [ rsp + 0x158 ]; x147, copying x142 here, cause x142 is needed in a reg for other than x147, namely all: , x147, size: 1
and r12, r11; x147 <- x142&0xffffffffffffff
adox rcx, r15
adox r10, rdx
mov r9, rcx; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x362, x363, size: 2
shrd r9, r10, 56; x362 <- x358||x356 >> 56
and rcx, r11; x363 <- x356&0xffffffffffffff
and rbp, r11; x337 <- x333&0xffffffffffffff
mov rax, [ rsp + 0x248 ]; TMP = x366
mov [ r14 + 0x38 ], rax; out1[7] = TMP
add rbp, [ rsp + 0x278 ]
lea r9, [ r9 + r12 ]
mov rax, r9; x367, copying x364 here, cause x364 is needed in a reg for other than x367, namely all: , x368, x367, size: 2
shr rax, 56; x367 <- x364>> 56
and r8, r11; x360 <- x351&0xffffffffffffff
and r9, r11; x368 <- x364&0xffffffffffffff
lea rax, [ rax + rbp ]
mov r15, rax; x373, copying x371 here, cause x371 is needed in a reg for other than x373, namely all: , x373, x372, size: 2
and r15, r11; x373 <- x371&0xffffffffffffff
and rbx, r11; x350 <- x341&0xffffffffffffff
shr rax, 56; x372 <- x371>> 56
mov [ r14 + 0x10 ], rcx; out1[2] = x363
and rdi, r11; x376 <- x370&0xffffffffffffff
lea rax, [ rax + rbx ]
mov [ r14 + 0x30 ], r8; out1[6] = x360
mov [ r14 + 0x20 ], r15; out1[4] = x373
mov [ r14 + 0x18 ], r9; out1[3] = x368
mov [ r14 + 0x28 ], rax; out1[5] = x374
mov [ r14 + 0x0 ], rdi; out1[0] = x376
mov rbx, [ rsp + 0x290 ]; restoring from stack
mov rbp, [ rsp + 0x298 ]; restoring from stack
mov r12, [ rsp + 0x2a0 ]; restoring from stack
mov r13, [ rsp + 0x2a8 ]; restoring from stack
mov r14, [ rsp + 0x2b0 ]; restoring from stack
mov r15, [ rsp + 0x2b8 ]; restoring from stack
add rsp, 0x2c0 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 255.74, best 175.81333333333333, lastGood 177.16883116883116
; seed 3549696848003676 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3220594 ms / 60000 runs=> 53.676566666666666ms/run
; Time spent for assembling and measureing (initial batch_size=77, initial num_batches=101): 218682 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.06790113873403478
; number reverted permutation/ tried permutation: 19169 / 29865 =64.186%
; number reverted decision/ tried decision: 19322 / 30136 =64.116%