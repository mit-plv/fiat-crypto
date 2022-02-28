SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x180 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x150 ], rbx; saving to stack
mov [ rsp + 0x158 ], rbp; saving to stack
mov [ rsp + 0x160 ], r12; saving to stack
mov [ rsp + 0x168 ], r13; saving to stack
mov [ rsp + 0x170 ], r14; saving to stack
mov [ rsp + 0x178 ], r15; saving to stack
mov rax, [ rsi + 0x38 ]; load m64 x4 to register64
mov r10, [ rsi + 0x40 ]; load m64 x1 to register64
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rbx, [ rsi + 0x0 ]; x106, x105<- arg1[0] * arg1[0]

; x2 <- x1 * 0x2 (by shlx'ing by 1 from reg)
shlx rbp, r10, 0x1

imul rbp, rbp, 0x2; x10001 <- x2 * 0x2
mov r13, [ rsi + 0x30 ]; load m64 x7 to register64
imul r14, rax, 0x2; x5 <- x4 * 0x2
shlx r15, [ rsi + 0x28 ], 0x1; x11 <- x10 (x10==arg1[5]) *2 (by shlx'ing by 1 (from mem))

imul r14, r14, 0x2; x10003 <- x5 * 0x2
imul rdx, r13, 0x2; x8 <- x7 * 0x2
imul rdx, rdx, 0x2; x10005 <- x8 * 0x2

; x10007 <- x11 * 2 (by shl 1)
shl r15, 0x1

xchg rdx, r14; x10003, swapping with x10005, which is currently in rdx
mulx rcx, r8, [ rsi + 0x10 ]; x62, x61<- arg1[2] * x10003
xchg rdx, r14; x10005, swapping with x10003, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, [ rsi + 0x18 ]; x52, x51<- arg1[3] * x10005
xchg rdx, rbp; x10001, swapping with x10005, which is currently in rdx
mov [ rsp + 0x8 ], r10; spilling x1 to mem
mov [ rsp + 0x10 ], r11; spilling x106 to mem
mulx r10, r11, [ rsi + 0x8 ]; x74, x73<- arg1[1] * x10001
xchg rdx, r15; x10007, swapping with x10001, which is currently in rdx
mov [ rsp + 0x18 ], r10; spilling x74 to mem
mulx rdx, r10, [ rsi + 0x20 ]; x44, x43<- arg1[4] * x10007
mov [ rsp + 0x20 ], rax; spilling x4 to mem
xor rax, rax
adox r10, rdi
adcx r10, r8
adox r9, rdx
mov rdx, r14; x10003 to rdx
mulx r14, r8, [ rsi + 0x18 ]; x50, x49<- arg1[3] * x10003
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, r11
adcx rcx, r9
mov r11, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r9, rax, rbp; x42, x41<- arg1[4] * x10005
clc;
adcx r10, rbx
setc dl; spill CF x120 to reg (rdx)
seto bl; spill OF x116 to reg (rbx)
imul r12, [ rsi + 0x28 ], 0x2; x10006 <- x10(x10==arg[5]) * 0x2
xchg rdx, r15; x10001, swapping with x120, which is currently in rdx
mov [ rsp + 0x28 ], r13; spilling x7 to mem
mulx rdi, r13, [ rsi + 0x10 ]; x60, x59<- arg1[2] * x10001
mov [ rsp + 0x30 ], rdi; spilling x60 to mem
mov rdi, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x38 ], r14; spilling x50 to mem
mulx r12, r14, r12; x36, x35<- arg1[5] * x10006
sar  bl, 1
adcx rcx, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x40 ], r12; spilling x36 to mem
mulx rbx, r12, [ rsi + 0x8 ]; x88, x87<- arg1[1] * arg1[1]
imul rdx, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
mov [ rsp + 0x48 ], rbx; spilling x88 to mem
mulx rdx, rbx, [ rsi + 0x0 ]; x104, x103<- arg1[0] * x16
sar  r15b, 1
adcx rcx, [ rsp + 0x10 ]
mov r15, r10; x123, copying x119 here, cause x119 is needed in a reg for other than x123, namely all: , x125, x123, size: 2
shrd r15, rcx, 58; x123 <- x121||x119 >> 58
test al, al
adox r14, rax
adcx r14, r8
setc r8b; spill CF x243 to reg (r8)
clc;
adcx r14, r13
adox r9, [ rsp + 0x40 ]
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, rbx
movzx r8, r8b
lea r9, [ r8 + r9 ]
mov r8, [ rsp + 0x38 ]
lea r9, [r8+r9]
adcx r9, [ rsp + 0x30 ]
clc;
adcx r14, r15
xchg rdx, r11; x10003, swapping with x104, which is currently in rdx
mulx r13, rbx, [ rsi + 0x20 ]; x40, x39<- arg1[4] * x10003
xchg rdx, rbp; x10005, swapping with x10003, which is currently in rdx
mulx rdx, r15, [ rsi + 0x28 ]; x34, x33<- arg1[5] * x10005
setc r8b; spill CF x255 to reg (r8)
seto al; spill OF x251 to reg (rax)
shr rcx, 58; x124 <- x121>> 58
mov [ rsp + 0x50 ], r12; spilling x87 to mem
imul r12, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
sar  al, 1
adcx r11, r9
sar  r8b, 1
adcx rcx, r11
mov rax, 0x3ffffffffffffff ; moving imm to reg
mov r9, r14; x260, copying x254 here, cause x254 is needed in a reg for other than x260, namely all: , x260, x258, size: 2
and r9, rax; x260 <- x254&0x3ffffffffffffff
shrd r14, rcx, 58; x258 <- x256||x254 >> 58
add r15, rbx; could be done better, if r0 has been u8 as well
mov r8, rdx; preserving value of x34 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, r11, rdi; x48, x47<- arg1[3] * x10001
setc dl; spill CF x223 to reg (rdx)
shr rcx, 58; x259 <- x256>> 58
mov al, dl; preserving value of x223 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x58 ], r9; spilling x260 to mem
mov [ rsp + 0x60 ], rcx; spilling x259 to mem
mulx r9, rcx, r12; x102, x101<- arg1[0] * x15
sar  al, 1
adcx r13, r8
adox r15, r11
adox rbx, r13
mov rdx, r12; x15 to rdx
mulx rdx, r12, [ rsi + 0x8 ]; x86, x85<- arg1[1] * x15
add r15, [ rsp + 0x50 ]; could be done better, if r0 has been u8 as well
adcx rbx, [ rsp + 0x48 ]
add r15, rcx; could be done better, if r0 has been u8 as well
setc r8b; spill CF x235 to reg (r8)
imul rax, [ rsp + 0x28 ], 0x2; x10004 <- x7 * 0x2
xchg rdx, rdi; x10001, swapping with x86, which is currently in rdx
mulx r11, rcx, [ rsi + 0x20 ]; x38, x37<- arg1[4] * x10001
xor r13, r13
adox r15, r14
movzx r8, r8b
lea r9, [ r9 + rbx ]
lea r9, [ r9 + r8 ]
seto r14b; spill OF x262 to reg (r14)
imul rbx, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
mov r8, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x68 ], rdi; spilling x86 to mem
mulx r13, rdi, rbp; x32, x31<- arg1[5] * x10003
sar  r14b, 1
adcx r9, [ rsp + 0x60 ]
mov rdx, r9; x266, copying x263 here, cause x263 is needed in a reg for other than x266, namely all: , x265, x266, size: 2
shr rdx, 58; x266 <- x263>> 58
xchg rdx, rbx; x14, swapping with x266, which is currently in rdx
mov [ rsp + 0x70 ], rbx; spilling x266 to mem
mulx r14, rbx, [ rsi + 0x0 ]; x100, x99<- arg1[0] * x14
mov [ rsp + 0x78 ], r14; spilling x100 to mem
mov r14, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x80 ], r11; spilling x38 to mem
mulx rax, r11, rax; x28, x27<- arg1[6] * x10004
add r11, rdi; could be done better, if r0 has been u8 as well
mov rdx, r14; x14 to rdx
mulx r14, rdi, [ rsi + 0x8 ]; x84, x83<- arg1[1] * x14
mov [ rsp + 0x88 ], r14; spilling x84 to mem
setc r14b; spill CF x207 to reg (r14)
mov [ rsp + 0x90 ], rdi; spilling x83 to mem
mov rdi, r15; x265, copying x261 here, cause x261 is needed in a reg for other than x265, namely all: , x267, x265, size: 2
shrd rdi, r9, 58; x265 <- x263||x261 >> 58
xor r9, r9
adox r11, rcx
seto cl; spill OF x211 to reg (rcx)
imul r9, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
sar  r14b, 1
adcx r13, rax
adox r11, r12
clc;
adcx r11, rbx
movzx rcx, cl
lea r13, [ rcx + r13 ]
mov rcx, [ rsp + 0x80 ]
lea r13, [rcx+r13]
seto r12b; spill OF x215 to reg (r12)
mov rbx, -0x2 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, rdi
setc al; spill CF x219 to reg (rax)
seto r14b; spill OF x269 to reg (r14)
imul rdi, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
sar  r12b, 1
adcx r13, [ rsp + 0x68 ]
sar  al, 1
adcx r13, [ rsp + 0x78 ]
xchg rdx, r8; x10001, swapping with x14, which is currently in rdx
mulx rcx, r12, [ rsi + 0x30 ]; x24, x23<- arg1[6] * x10001
mulx rax, rbx, [ rsi + 0x28 ]; x30, x29<- arg1[5] * x10001
xchg rdx, rbp; x10003, swapping with x10001, which is currently in rdx
mov [ rsp + 0x98 ], r9; spilling x6 to mem
mulx rdx, r9, [ rsi + 0x30 ]; x26, x25<- arg1[6] * x10003
xchg rdx, rdi; x13, swapping with x26, which is currently in rdx
mov [ rsp + 0xa0 ], rcx; spilling x24 to mem
mov [ rsp + 0xa8 ], r12; spilling x23 to mem
mulx rcx, r12, [ rsi + 0x0 ]; x98, x97<- arg1[0] * x13
sar  r14b, 1
adcx r13, [ rsp + 0x70 ]
mov r14, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xb0 ], r10; spilling x119 to mem
mov [ rsp + 0xb8 ], rcx; spilling x98 to mem
mulx r10, rcx, [ rsi + 0x10 ]; x72, x71<- arg1[2] * arg1[2]
mov rdx, r11; x272, copying x268 here, cause x268 is needed in a reg for other than x272, namely all: , x272, x274, size: 2
shrd rdx, r13, 58; x272 <- x270||x268 >> 58
test al, al
adox r9, rbx
adox rax, rdi
shr r13, 58; x273 <- x270>> 58
test al, al
adox r9, rcx
adcx r9, [ rsp + 0x90 ]
adox r10, rax
adcx r10, [ rsp + 0x88 ]
xor rbx, rbx
adox r9, r12
adox r10, [ rsp + 0xb8 ]
imul rdi, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
xchg rdx, r8; x14, swapping with x272, which is currently in rdx
mulx rdx, r12, [ rsi + 0x10 ]; x70, x69<- arg1[2] * x14
test al, al
adox r9, r8
adox r13, r10
imul rcx, [ rsp + 0x20 ], 0x2; x10002 <- x4 * 0x2
mov r8, rdx; preserving value of x70 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx rcx, rax, rcx; x22, x21<- arg1[7] * x10002
mov rdx, r14; x13 to rdx
mulx r14, r10, [ rsi + 0x8 ]; x82, x81<- arg1[1] * x13
xchg rdx, rdi; x12, swapping with x13, which is currently in rdx
mov [ rsp + 0xc0 ], r14; spilling x82 to mem
mulx rbx, r14, [ rsi + 0x8 ]; x80, x79<- arg1[1] * x12
mov [ rsp + 0xc8 ], rbx; spilling x80 to mem
mov rbx, r9; x279, copying x275 here, cause x275 is needed in a reg for other than x279, namely all: , x281, x279, size: 2
shrd rbx, r13, 58; x279 <- x277||x275 >> 58
shr r13, 58; x280 <- x277>> 58
mov [ rsp + 0xd0 ], r14; spilling x79 to mem
xor r14, r14
adox rax, [ rsp + 0xa8 ]
adox rcx, [ rsp + 0xa0 ]
adcx rax, r12
adcx r8, rcx
add rax, r10; could be done better, if r0 has been u8 as well
mulx r12, r10, [ rsi + 0x0 ]; x96, x95<- arg1[0] * x12
xchg rdx, rbp; x10001, swapping with x12, which is currently in rdx
mulx rdx, rcx, [ rsi + 0x38 ]; x20, x19<- arg1[7] * x10001
adcx r8, [ rsp + 0xc0 ]
mov r14, rdx; preserving value of x20 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xd8 ], r13; spilling x280 to mem
mov [ rsp + 0xe0 ], r8; spilling x184 to mem
mulx r13, r8, [ rsi + 0x18 ]; x58, x57<- arg1[3] * arg1[3]
xor rdx, rdx
adox rax, r10
adcx rcx, r8
setc r10b; spill CF x159 to reg (r10)
seto r8b; spill OF x187 to reg (r8)
imul rdx, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
sar  r10b, 1
adcx r13, r14
adox rax, rbx
movzx r8, r8b
lea r12, [ r8 + r12 ]
mov r8, [ rsp + 0xe0 ]
lea r12, [r8+r12]
adox r12, [ rsp + 0xd8 ]
mov rbx, rax; x286, copying x282 here, cause x282 is needed in a reg for other than x286, namely all: , x288, x286, size: 2
shrd rbx, r12, 58; x286 <- x284||x282 >> 58
xchg rdx, rdi; x13, swapping with x9, which is currently in rdx
mulx r14, r8, [ rsi + 0x10 ]; x68, x67<- arg1[2] * x13
shr r12, 58; x287 <- x284>> 58
add rcx, r8; could be done better, if r0 has been u8 as well
xchg rdx, rdi; x9, swapping with x13, which is currently in rdx
mulx r10, r8, [ rsi + 0x0 ]; x94, x93<- arg1[0] * x9
mov [ rsp + 0xe8 ], r12; spilling x287 to mem
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0xd0 ]
adcx r14, r13
clc;
adcx rcx, r8
adox r14, [ rsp + 0xc8 ]
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rcx, rbx
mov r13, rdx; preserving value of x9 into a new reg
mov rdx, [ rsp + 0x98 ]; saving x6 in rdx.
mulx rbx, r8, [ rsi + 0x0 ]; x92, x91<- arg1[0] * x6
adcx r10, r14
seto r14b; spill OF x290 to reg (r14)
imul r12, [ rsp + 0x8 ], 0x2; x10000 <- x1 * 0x2
xchg rdx, rdi; x13, swapping with x6, which is currently in rdx
mov [ rsp + 0xf0 ], rbx; spilling x92 to mem
mulx rdx, rbx, [ rsi + 0x18 ]; x56, x55<- arg1[3] * x13
xchg rdx, r12; x10000, swapping with x56, which is currently in rdx
mov [ rsp + 0xf8 ], r8; spilling x91 to mem
mulx rdx, r8, [ rsi + 0x40 ]; x18, x17<- arg1[8] * x10000
xchg rdx, r13; x9, swapping with x18, which is currently in rdx
mov [ rsp + 0x100 ], r13; spilling x18 to mem
mov [ rsp + 0x108 ], r12; spilling x56 to mem
mulx r13, r12, [ rsi + 0x8 ]; x78, x77<- arg1[1] * x9
sar  r14b, 1
adcx r10, [ rsp + 0xe8 ]
xchg rdx, rbp; x12, swapping with x9, which is currently in rdx
mov [ rsp + 0x110 ], r13; spilling x78 to mem
mulx r14, r13, [ rsi + 0x18 ]; x54, x53<- arg1[3] * x12
adox r8, rbx
seto bl; spill OF x143 to reg (rbx)
mov [ rsp + 0x118 ], r14; spilling x54 to mem
mov r14, r10; x294, copying x291 here, cause x291 is needed in a reg for other than x294, namely all: , x293, x294, size: 2
shr r14, 58; x294 <- x291>> 58
mov [ rsp + 0x120 ], r13; spilling x53 to mem
mulx rdx, r13, [ rsi + 0x10 ]; x66, x65<- arg1[2] * x12
mov [ rsp + 0x128 ], r14; spilling x294 to mem
mov r14, rcx; x293, copying x289 here, cause x289 is needed in a reg for other than x293, namely all: , x295, x293, size: 2
shrd r14, r10, 58; x293 <- x291||x289 >> 58
add r8, r13; could be done better, if r0 has been u8 as well
mov r10, [ rsp + 0x108 ]; load m64 x56 to register64
movzx rbx, bl
lea r10, [ rbx + r10 ]
mov rbx, [ rsp + 0x100 ]
lea r10, [rbx+r10]
adcx rdx, r10
add r8, r12; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x110 ]
mov r12, rdx; preserving value of x152 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbx, r13, [ rsi + 0x20 ]; x46, x45<- arg1[4] * arg1[4]
imul rdx, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
xor r10, r10
adox r8, [ rsp + 0xf8 ]
adox r12, [ rsp + 0xf0 ]
adcx r8, r14
adcx r12, [ rsp + 0x128 ]
mulx rdx, r14, [ rsi + 0x0 ]; x90, x89<- arg1[0] * x3
add r13, [ rsp + 0x120 ]; could be done better, if r0 has been u8 as well
mov r10, rdx; preserving value of x90 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x130 ], r14; spilling x89 to mem
mulx rdi, r14, rdi; x76, x75<- arg1[1] * x6
mov rdx, 0x3ffffffffffffff ; moving imm to reg
mov [ rsp + 0x138 ], r10; spilling x90 to mem
setc r10b; spill CF x127 to reg (r10)
mov [ rsp + 0x140 ], rdi; spilling x76 to mem
mov rdi, [ rsp + 0xb0 ]; x125, copying x119 here, cause x119 is needed in a reg for other than x125, namely all: , x125, size: 1
and rdi, rdx; x125 <- x119&0x3ffffffffffffff
xchg rdx, rbp; x9, swapping with 0x3ffffffffffffff, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x10 ]; x64, x63<- arg1[2] * x9
mov [ rsp + 0x148 ], rdi; spilling x125 to mem
mov rdi, r8; x300, copying x296 here, cause x296 is needed in a reg for other than x300, namely all: , x302, x300, size: 2
shrd rdi, r12, 58; x300 <- x298||x296 >> 58
shr r12, 58; x301 <- x298>> 58
test al, al
adox r13, rbp
movzx r10, r10b
lea rbx, [ r10 + rbx ]
adcx rbx, [ rsp + 0x118 ]
adox rdx, rbx
test al, al
adox r13, r14
adcx r13, [ rsp + 0x130 ]
adox rdx, [ rsp + 0x140 ]
adcx rdx, [ rsp + 0x138 ]
xor r10, r10
adox r13, rdi
adox r12, rdx
mov r14, r13; x307, copying x303 here, cause x303 is needed in a reg for other than x307, namely all: , x309, x307, size: 2
shrd r14, r12, 57; x307 <- x305||x303 >> 57
shr r12, 57; x308 <- x305>> 57
xor rbp, rbp
adox r14, [ rsp + 0x148 ]
adox r12, rbp
mov r10, 0x3ffffffffffffff ; moving imm to reg
and r15, r10; x267 <- x261&0x3ffffffffffffff
mov rdi, r14; x313, copying x310 here, cause x310 is needed in a reg for other than x313, namely all: , x313, x314, size: 2
shrd rdi, r12, 58; x313 <- x312||x310 >> 58
add rdi, [ rsp + 0x58 ]
and r9, r10; x281 <- x275&0x3ffffffffffffff
mov rbx, rdi; x316, copying x315 here, cause x315 is needed in a reg for other than x316, namely all: , x316, x317, size: 2
shr rbx, 58; x316 <- x315>> 58
mov rdx, 0x1ffffffffffffff ; moving imm to reg
and r13, rdx; x309 <- x303&0x1ffffffffffffff
and rax, r10; x288 <- x282&0x3ffffffffffffff
and rdi, r10; x317 <- x315&0x3ffffffffffffff
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x28 ], rax; out1[5] = x288
lea rbx, [ rbx + r15 ]
mov [ r12 + 0x20 ], r9; out1[4] = x281
and r11, r10; x274 <- x268&0x3ffffffffffffff
mov [ r12 + 0x18 ], r11; out1[3] = x274
and r8, r10; x302 <- x296&0x3ffffffffffffff
mov [ r12 + 0x38 ], r8; out1[7] = x302
mov [ r12 + 0x40 ], r13; out1[8] = x309
and r14, r10; x314 <- x310&0x3ffffffffffffff
mov [ r12 + 0x0 ], r14; out1[0] = x314
and rcx, r10; x295 <- x289&0x3ffffffffffffff
mov [ r12 + 0x10 ], rbx; out1[2] = x318
mov [ r12 + 0x30 ], rcx; out1[6] = x295
mov [ r12 + 0x8 ], rdi; out1[1] = x317
mov rbx, [ rsp + 0x150 ]; restoring from stack
mov rbp, [ rsp + 0x158 ]; restoring from stack
mov r12, [ rsp + 0x160 ]; restoring from stack
mov r13, [ rsp + 0x168 ]; restoring from stack
mov r14, [ rsp + 0x170 ]; restoring from stack
mov r15, [ rsp + 0x178 ]; restoring from stack
add rsp, 0x180 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 129.54, best 89.51898734177215, lastGood 90.1
; seed 600995032503849 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1565922 ms / 60000 runs=> 26.0987ms/run
; Time spent for assembling and measureing (initial batch_size=79, initial num_batches=101): 135415 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.08647621018160546
; number reverted permutation/ tried permutation: 22780 / 29920 =76.136%
; number reverted decision/ tried decision: 21428 / 30081 =71.234%
