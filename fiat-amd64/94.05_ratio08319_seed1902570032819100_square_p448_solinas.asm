SECTION .text
	GLOBAL square_p448_solinas
square_p448_solinas:
sub rsp, 0x250 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x220 ], rbx; saving to stack
mov [ rsp + 0x228 ], rbp; saving to stack
mov [ rsp + 0x230 ], r12; saving to stack
mov [ rsp + 0x238 ], r13; saving to stack
mov [ rsp + 0x240 ], r14; saving to stack
mov [ rsp + 0x248 ], r15; saving to stack
imul rax, [ rsi + 0x10 ], 0x2; x20 <- arg1[2] * 0x2
mov r10, [ rsi + 0x38 ]; load m64 x2 to register64
mov r11, [ rsi + 0x28 ]; load m64 x11 to register64
imul rbx, [ rsi + 0x18 ], 0x2; x19 <- arg1[3] * 0x2
imul rbp, r10, 0x2; x4 <- x2 * 0x2
mov rdx, rbp; x4 to rdx
mulx rbp, r12, [ rsi + 0x20 ]; x55, x54<- arg1[4] * x4
mov r13, [ rsi + 0x30 ]; load m64 x7 to register64
imul r14, r13, 0x2; x9 <- x7 * 0x2
mov r15, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rcx, r8, r14; x47, x46<- arg1[5] * x9
mov rdx, rax; x20 to rdx
mulx rax, r9, [ rsi + 0x8 ]; x115, x114<- arg1[1] * x20
add r8, r12; could be done better, if r0 has been u8 as well
adcx rbp, rcx
xchg rdx, rbx; x19, swapping with x20, which is currently in rdx
mulx r12, rcx, [ rsi + 0x0 ]; x127, x126<- arg1[0] * x19
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
imul rdi, [ rsi + 0x20 ], 0x2; x18 <- arg1[4] * 0x2
mov [ rsp + 0x8 ], r10; spilling x2 to mem
mov r10, [ rsi + 0x38 ]; load m64 x1 to register64
mov [ rsp + 0x10 ], r15; spilling x4 to mem
mov [ rsp + 0x18 ], rdi; spilling x18 to mem
mulx r15, rdi, [ rsi + 0x8 ]; x113, x112<- arg1[1] * x19
add r8, r9; could be done better, if r0 has been u8 as well
adcx rax, rbp
add r8, rcx; could be done better, if r0 has been u8 as well
setc r9b; spill CF x143 to reg (r9)
imul rbp, r10, 0x2; x3 <- x1 * 0x2
mov rcx, [ rsi + 0x20 ]; load m64 x16 to register64
mov [ rsp + 0x20 ], r15; spilling x113 to mem
mov r15, [ rsi + 0x30 ]; load m64 x6 to register64
mov [ rsp + 0x28 ], r14; spilling x9 to mem
imul r14, r11, 0x2; x13 <- x11 * 0x2
sar  r9b, 1
adcx r12, rax
mov rax, r8; x146, copying x142 here, cause x142 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd rax, r12, 56; x146 <- x144||x142 >> 56
imul r9, r15, 0x2; x8 <- x6 * 0x2
mov r12, rdx; preserving value of x19 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x30 ], rbx; spilling x20 to mem
mov [ rsp + 0x38 ], rax; spilling x146 to mem
mulx rbx, rax, rbp; x37, x36<- arg1[5] * x3
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x40 ], rdi; spilling x112 to mem
mov [ rsp + 0x48 ], rbx; spilling x37 to mem
mulx rdi, rbx, rbp; x105, x104<- arg1[1] * x3
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x50 ], rdi; spilling x105 to mem
mov [ rsp + 0x58 ], rbx; spilling x104 to mem
mulx rdi, rbx, r15; x35, x34<- arg1[6] * x6
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x60 ], rdi; spilling x35 to mem
mov [ rsp + 0x68 ], r9; spilling x8 to mem
mulx rdi, r9, [ rsi + 0x10 ]; x101, x100<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x70 ], rdi; spilling x101 to mem
mov [ rsp + 0x78 ], r9; spilling x100 to mem
mulx rdi, r9, r14; x81, x80<- arg1[3] * x13
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x80 ], rdi; spilling x81 to mem
mov [ rsp + 0x88 ], r9; spilling x80 to mem
mulx rdi, r9, [ rsp + 0x18 ]; x125, x124<- arg1[0] * x18
mov rdx, r13; x7 to rdx
mulx rdx, r13, [ rsi + 0x30 ]; x43, x42<- arg1[6] * x7
mov [ rsp + 0x90 ], rdi; spilling x125 to mem
mov rdi, rdx; preserving value of x43 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x98 ], r9; spilling x124 to mem
mulx rcx, r9, rcx; x69, x68<- arg1[4] * x16
xor rdx, rdx
adox rbx, rax
mov rax, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0xa0 ], rcx; spilling x69 to mem
mov [ rsp + 0xa8 ], rdi; spilling x43 to mem
mulx rcx, rdi, [ rsp + 0x10 ]; x45, x44<- arg1[5] * x4
adcx rbx, r13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r13, rax, [ rsp + 0x68 ]; x93, x92<- arg1[2] * x8
setc dl; spill CF x233 to reg (rdx)
clc;
adcx rbx, rdi
seto dil; spill OF x229 to reg (rdi)
mov [ rsp + 0xb0 ], r13; spilling x93 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, r9
setc r9b; spill CF x237 to reg (r9)
seto r13b; spill OF x241 to reg (r13)
mov [ rsp + 0xb8 ], rcx; spilling x45 to mem
imul rcx, [ rsi + 0x28 ], 0x2; x15 <- arg1[5] * 0x2
test al, al
adox rbx, [ rsp + 0x88 ]
adcx rbx, rax
seto al; spill OF x245 to reg (rax)
mov [ rsp + 0xc0 ], r12; spilling x19 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, [ rsp + 0x78 ]
setc r12b; spill CF x249 to reg (r12)
mov byte [ rsp + 0xc8 ], al; spilling byte x245 to mem
seto al; spill OF x253 to reg (rax)
mov [ rsp + 0xd0 ], rcx; spilling x15 to mem
imul rcx, [ rsi + 0x30 ], 0x2; x10 <- arg1[6] * 0x2
mov byte [ rsp + 0xd8 ], al; spilling byte x253 to mem
mov al, dl; preserving value of x233 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov byte [ rsp + 0xe0 ], r12b; spilling byte x249 to mem
mov byte [ rsp + 0xe8 ], r13b; spilling byte x241 to mem
mulx r12, r13, rcx; x107, x106<- arg1[1] * x10
mov rdx, [ rsp + 0x60 ]; load m64 x35 to register64
sar  dil, 1
adcx rdx, [ rsp + 0x48 ]
sar  al, 1
adcx rdx, [ rsp + 0xa8 ]
adox rbx, [ rsp + 0x58 ]
mov rdi, rdx; preserving value of x234 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xf0 ], r12; spilling x107 to mem
mulx rax, r12, [ rsp + 0x18 ]; x83, x82<- arg1[3] * x18
seto dl; spill OF x257 to reg (rdx)
mov [ rsp + 0xf8 ], r13; spilling x106 to mem
imul r13, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov [ rsp + 0x100 ], r13; spilling x5 to mem
mov r13b, dl; preserving value of x257 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x108 ], rax; spilling x83 to mem
mov [ rsp + 0x110 ], r12; spilling x82 to mem
mulx rax, r12, rbp; x57, x56<- arg1[4] * x3
sar  r9b, 1
adcx rdi, [ rsp + 0xb8 ]
adox rbx, [ rsp + 0x40 ]
clc;
adcx rbx, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x118 ], r10; spilling x1 to mem
mulx r9, r10, [ rsp + 0x68 ]; x49, x48<- arg1[5] * x8
seto dl; spill OF x261 to reg (rdx)
mov byte [ rsp + 0x120 ], r13b; spilling byte x257 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r12
adox rax, r9
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, [ rsp + 0x38 ]
seto r12b; spill OF x329 to reg (r12)
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, [ rsp + 0x110 ]
movzx r13, byte [ rsp + 0xe8 ]; load byte memx241 to register64
lea rdi, [ r13 + rdi ]
mov r13, [ rsp + 0xa0 ]
lea rdi, [r13+rdi]
mov r13b, dl; preserving value of x261 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x128 ], r11; spilling x11 to mem
mulx r9, r11, [ rsp + 0xd0 ]; x95, x94<- arg1[2] * x15
movzx rdx, byte [ rsp + 0xc8 ]; load byte memx245 to register64
lea rdi, [ rdx + rdi ]
mov rdx, [ rsp + 0x80 ]
lea rdi, [rdx+rdi]
setc dl; spill CF x265 to reg (rdx)
clc;
adcx r10, r11
adox rax, [ rsp + 0x108 ]
mov r11b, dl; preserving value of x265 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x130 ], r8; spilling x142 to mem
mov [ rsp + 0x138 ], rbx; spilling x328 to mem
mulx r8, rbx, [ rsp + 0x100 ]; x119, x118<- arg1[0] * x5
adcx r9, rax
sar byte [ rsp + 0xe0 ], 1
adcx rdi, [ rsp + 0xb0 ]
adox r10, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, rax, r14; x65, x64<- arg1[4] * x13
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x140 ], r14; spilling x65 to mem
mov [ rsp + 0x148 ], rax; spilling x64 to mem
mulx r14, rax, rbp; x33, x32<- arg1[6] * x3
movzx rdx, byte [ rsp + 0xd8 ]; load byte memx253 to register64
lea rdi, [ rdx + rdi ]
mov rdx, [ rsp + 0x70 ]
lea rdi, [rdx+rdi]
clc;
adcx r10, rbx
movzx rdx, byte [ rsp + 0x120 ]; load byte memx257 to register64
lea rdi, [ rdx + rdi ]
mov rdx, [ rsp + 0x50 ]
lea rdi, [rdx+rdi]
adox r9, [ rsp + 0xf0 ]
movzx r13, r13b
lea rdi, [ r13 + rdi ]
mov r13, [ rsp + 0x20 ]
lea rdi, [r13+rdi]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r13, rbx, [ rsp + 0x10 ]; x41, x40<- arg1[6] * x4
adcx r8, r9
sar  r11b, 1
adcx rdi, [ rsp + 0x90 ]
movzx rdx, r12b; x330, copying x329 here, cause x329 is needed in a reg for other than x330, namely all: , x330, size: 1
lea rdx, [ rdx + rdi ]
mov r11, r10; x331, copying x164 here, cause x164 is needed in a reg for other than x331, namely all: , x332, x331, size: 2
shrd r11, r8, 56; x331 <- x166||x164 >> 56
mov r12, rdx; preserving value of x330 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r9, r8, [ rsp + 0xc0 ]; x99, x98<- arg1[2] * x19
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x150 ], r15; spilling x6 to mem
mulx rdi, r15, [ rsp + 0xd0 ]; x123, x122<- arg1[0] * x15
xor rdx, rdx
adox rax, rbx
mov rbx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x158 ], rdi; spilling x123 to mem
mov [ rsp + 0x160 ], r15; spilling x122 to mem
mulx rdi, r15, [ rsi + 0x18 ]; x85, x84<- arg1[3] * arg1[3]
adox r13, r14
mov rdx, [ rsp + 0x68 ]; x8 to rdx
mulx r14, rbx, [ rsi + 0x18 ]; x77, x76<- arg1[3] * x8
mov [ rsp + 0x168 ], rdi; spilling x85 to mem
mov rdi, r11; x333, copying x331 here, cause x331 is needed in a reg for other than x333, namely all: , x338--x339, x333--x334, size: 2
adcx rdi, [ rsp + 0x138 ]
adc r12, 0x0
mov [ rsp + 0x170 ], r15; spilling x84 to mem
mov r15, rdi; x336, copying x333 here, cause x333 is needed in a reg for other than x336, namely all: , x336, x337, size: 2
shrd r15, r12, 56; x336 <- x335||x333 >> 56
mov r12, rdx; preserving value of x8 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x178 ], r15; spilling x336 to mem
mov [ rsp + 0x180 ], r9; spilling x99 to mem
mulx r15, r9, [ rsp + 0x18 ]; x111, x110<- arg1[1] * x18
mov rdx, rbp; x3 to rdx
mov [ rsp + 0x188 ], r15; spilling x111 to mem
mulx rbp, r15, [ rsi + 0x10 ]; x89, x88<- arg1[2] * x3
add rax, [ rsp + 0x148 ]; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x140 ]
test al, al
adox rax, rbx
adox r14, r13
adcx rax, r15
mov rbx, rdx; preserving value of x3 into a new reg
mov rdx, [ rsp + 0x8 ]; saving x2 in rdx.
mulx rdx, r15, [ rsi + 0x38 ]; x39, x38<- arg1[7] * x2
adcx rbp, r14
xor r13, r13
adox rax, r8
adox rbp, [ rsp + 0x180 ]
adcx rax, r9
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rax, [ rsp + 0x160 ]
adcx rbp, [ rsp + 0x188 ]
mov r9, rdx; preserving value of x39 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r14, r13, rbx; x73, x72<- arg1[3] * x3
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x190 ], r14; spilling x73 to mem
mulx r8, r14, [ rsp + 0x18 ]; x97, x96<- arg1[2] * x18
clc;
adcx rax, [ rsp + 0x178 ]
mov rdx, [ rsp + 0xd0 ]; x15 to rdx
mov [ rsp + 0x198 ], r8; spilling x97 to mem
mulx rdx, r8, [ rsi + 0x8 ]; x109, x108<- arg1[1] * x15
adox rbp, [ rsp + 0x158 ]
mov [ rsp + 0x1a0 ], r8; spilling x108 to mem
mov r8, rdx; preserving value of x109 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x1a8 ], r14; spilling x96 to mem
mulx r12, r14, r12; x61, x60<- arg1[4] * x8
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x1b0 ], r8; spilling x109 to mem
mov [ rsp + 0x1b8 ], r12; spilling x61 to mem
mulx r8, r12, [ rsp + 0x118 ]; x31, x30<- arg1[7] * x1
adc rbp, 0x0
add r12, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsp + 0x128 ]; x11 to rdx
mulx rdx, r15, [ rsi + 0x28 ]; x53, x52<- arg1[5] * x11
mov [ rsp + 0x1c0 ], r13; spilling x72 to mem
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r15
adcx r9, r8
adox rdx, r9
mov r8, rax; x349, copying x341 here, cause x341 is needed in a reg for other than x349, namely all: , x350, x349, size: 2
shrd r8, rbp, 56; x349 <- x343||x341 >> 56
add r12, r14; could be done better, if r0 has been u8 as well
mov r14, [ rsi + 0x20 ]; load m64 x17 to register64
inc r13; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp + 0x1c0 ]
mov rbp, [ rsi + 0x28 ]; load m64 x12 to register64
adcx rdx, [ rsp + 0x1b8 ]
adox rdx, [ rsp + 0x190 ]
xor r15, r15
adox r12, [ rsp + 0x170 ]
adox rdx, [ rsp + 0x168 ]
adcx r12, [ rsp + 0x1a8 ]
adcx rdx, [ rsp + 0x198 ]
mov r13, rdx; preserving value of x190 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rcx, r9, rcx; x121, x120<- arg1[0] * x10
xor rdx, rdx
adox r12, [ rsp + 0x1a0 ]
adcx r12, r9
adox r13, [ rsp + 0x1b0 ]
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r12, r8
mov r8, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsp + 0x150 ]; saving x6 in rdx.
mulx rdx, r9, [ rsi + 0x30 ]; x27, x26<- arg1[6] * x6
adcx rcx, r13
xchg rdx, r14; x17, swapping with x27, which is currently in rdx
mulx rdx, r13, [ rsi + 0x20 ]; x67, x66<- arg1[4] * x17
adox rcx, r8
mov r8, r12; x359, copying x351 here, cause x351 is needed in a reg for other than x359, namely all: , x359, x360, size: 2
shrd r8, rcx, 56; x359 <- x353||x351 >> 56
mov rcx, 0xffffffffffffff ; moving imm to reg
and r10, rcx; x332 <- x164&0xffffffffffffff
mov r15, rdx; preserving value of x67 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x1c8 ], r14; spilling x27 to mem
mulx rcx, r14, [ rsp + 0x28 ]; x91, x90<- arg1[2] * x9
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1d0 ], rcx; spilling x91 to mem
mov [ rsp + 0x1d8 ], r14; spilling x90 to mem
mulx rcx, r14, [ rsi + 0x0 ]; x133, x132<- arg1[0] * arg1[0]
mov rdx, rbx; x3 to rdx
mov [ rsp + 0x1e0 ], rcx; spilling x133 to mem
mulx rbx, rcx, [ rsi + 0x28 ]; x29, x28<- arg1[5] * x3
lea r8, [ r8 + r10 ]
imul r10, rbp, 0x2; x14 <- x12 * 0x2
mov [ rsp + 0x1e8 ], r8; spilling x361 to mem
xor r8, r8
adox r9, rcx
adcx r9, r13
mov r13, rdx; preserving value of x3 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rcx, r8, r10; x79, x78<- arg1[3] * x14
adox rbx, [ rsp + 0x1c8 ]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, r8
adcx r15, rbx
adox rcx, r15
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, rbx, [ rsp + 0x10 ]; x103, x102<- arg1[1] * x4
add r9, [ rsp + 0x1d8 ]; could be done better, if r0 has been u8 as well
mov rdx, r10; x14 to rdx
mulx rdx, r10, [ rsi + 0x20 ]; x63, x62<- arg1[4] * x14
mov r15, -0x2 ; moving imm to reg
inc r15; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r9, rbx
adcx rcx, [ rsp + 0x1d0 ]
adox r8, rcx
mov rbx, rdx; preserving value of x63 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rcx, r15, [ rsp + 0x28 ]; x75, x74<- arg1[3] * x9
add r9, r14; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mulx r13, r14, r13; x25, x24<- arg1[6] * x3
adcx r8, [ rsp + 0x1e0 ]
test al, al
adox r14, r10
mov rdx, [ rsp + 0x10 ]; x4 to rdx
mov [ rsp + 0x1f0 ], rcx; spilling x75 to mem
mulx r10, rcx, [ rsi + 0x10 ]; x87, x86<- arg1[2] * x4
adcx r11, r9
adox rbx, r13
adc r8, 0x0
imul r9, [ rsi + 0x8 ], 0x2; x21 <- arg1[1] * 0x2
mov r13, r11; x344, copying x338 here, cause x338 is needed in a reg for other than x344, namely all: , x345, x344, size: 2
shrd r13, r8, 56; x344 <- x340||x338 >> 56
xor r8, r8
adox r14, r15
adcx r14, rcx
mov r15, rdx; preserving value of x4 into a new reg
mov rdx, [ rsp + 0x30 ]; saving x20 in rdx.
mulx rdx, rcx, [ rsi + 0x0 ]; x129, x128<- arg1[0] * x20
mov r8, rdx; preserving value of x129 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x1f8 ], rcx; spilling x128 to mem
mulx r9, rcx, r9; x131, x130<- arg1[0] * x21
adox rbx, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x200 ], r8; spilling x129 to mem
mulx r15, r8, r15; x71, x70<- arg1[3] * x4
adcx r10, rbx
add r14, rcx; could be done better, if r0 has been u8 as well
adcx r9, r10
add r14, r13; could be done better, if r0 has been u8 as well
adc r9, 0x0
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r13, rcx, [ rsp + 0x118 ]; x23, x22<- arg1[7] * x1
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r10, [ rsi + 0x8 ]; x117, x116<- arg1[1] * arg1[1]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x208 ], rbx; spilling x117 to mem
mulx rbp, rbx, rbp; x51, x50<- arg1[5] * x12
mov rdx, r14; x354, copying x346 here, cause x346 is needed in a reg for other than x354, namely all: , x355, x354, size: 2
shrd rdx, r9, 56; x354 <- x348||x346 >> 56
mov r9, rdx; preserving value of x354 into a new reg
mov rdx, [ rsp + 0x28 ]; saving x9 in rdx.
mov [ rsp + 0x210 ], r10; spilling x116 to mem
mulx rdx, r10, [ rsi + 0x20 ]; x59, x58<- arg1[4] * x9
mov [ rsp + 0x218 ], r9; spilling x354 to mem
xor r9, r9
adox rcx, rbx
adox rbp, r13
adcx rcx, r10
adcx rdx, rbp
xor r13, r13
adox rcx, r8
adox r15, rdx
mov r9, 0xffffffffffffff ; moving imm to reg
and rdi, r9; x337 <- x333&0xffffffffffffff
adox rcx, [ rsp + 0x210 ]
adox r15, [ rsp + 0x208 ]
adcx rcx, [ rsp + 0x1f8 ]
setc r8b; spill CF x285 to reg (r8)
mov rbx, [ rsp + 0x1e8 ]; x366, copying x361 here, cause x361 is needed in a reg for other than x366, namely all: , x366, x365, size: 2
and rbx, r9; x366 <- x361&0xffffffffffffff
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x38 ], rbx; out1[7] = x366
and r11, r9; x345 <- x338&0xffffffffffffff
mov rbp, [ rsp + 0x1e8 ]; x365, copying x361 here, cause x361 is needed in a reg for other than x365, namely all: , x365, size: 1
shr rbp, 56; x365 <- x361>> 56
mov rdx, [ rsp + 0x130 ]; x147, copying x142 here, cause x142 is needed in a reg for other than x147, namely all: , x147, size: 1
and rdx, r9; x147 <- x142&0xffffffffffffff
sar  r8b, 1
adcx r15, [ rsp + 0x200 ]
adox rcx, [ rsp + 0x218 ]
adox r15, r13
lea r11, [ r11 + rbp ]
mov r8, rcx; x362, copying x356 here, cause x356 is needed in a reg for other than x362, namely all: , x362, x363, size: 2
shrd r8, r15, 56; x362 <- x358||x356 >> 56
mov rbx, r11; x375, copying x370 here, cause x370 is needed in a reg for other than x375, namely all: , x375, x376, size: 2
shr rbx, 56; x375 <- x370>> 56
and r12, r9; x360 <- x351&0xffffffffffffff
lea rdi, [ rdi + rbp ]
lea r8, [ r8 + rdx ]
mov rbp, r8; x367, copying x364 here, cause x364 is needed in a reg for other than x367, namely all: , x368, x367, size: 2
shr rbp, 56; x367 <- x364>> 56
lea rbp, [ rbp + rdi ]
and rax, r9; x350 <- x341&0xffffffffffffff
mov rdx, rbp; x372, copying x371 here, cause x371 is needed in a reg for other than x372, namely all: , x372, x373, size: 2
shr rdx, 56; x372 <- x371>> 56
and r11, r9; x376 <- x370&0xffffffffffffff
mov [ r10 + 0x30 ], r12; out1[6] = x360
and r8, r9; x368 <- x364&0xffffffffffffff
and r14, r9; x355 <- x346&0xffffffffffffff
and rcx, r9; x363 <- x356&0xffffffffffffff
mov [ r10 + 0x18 ], r8; out1[3] = x368
lea rdx, [ rdx + rax ]
lea rbx, [ rbx + r14 ]
and rbp, r9; x373 <- x371&0xffffffffffffff
mov [ r10 + 0x20 ], rbp; out1[4] = x373
mov [ r10 + 0x10 ], rcx; out1[2] = x363
mov [ r10 + 0x8 ], rbx; out1[1] = x377
mov [ r10 + 0x28 ], rdx; out1[5] = x374
mov [ r10 + 0x0 ], r11; out1[0] = x376
mov rbx, [ rsp + 0x220 ]; restoring from stack
mov rbp, [ rsp + 0x228 ]; restoring from stack
mov r12, [ rsp + 0x230 ]; restoring from stack
mov r13, [ rsp + 0x238 ]; restoring from stack
mov r14, [ rsp + 0x240 ]; restoring from stack
mov r15, [ rsp + 0x248 ]; restoring from stack
add rsp, 0x250 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 135.525, best 93.60162601626017, lastGood 94.048
; seed 1902570032819100 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1839103 ms / 60000 runs=> 30.651716666666665ms/run
; Time spent for assembling and measureing (initial batch_size=125, initial num_batches=101): 163036 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.08864973848664268
; number reverted permutation/ tried permutation: 20436 / 29920 =68.302%
; number reverted decision/ tried decision: 21240 / 30081 =70.609%