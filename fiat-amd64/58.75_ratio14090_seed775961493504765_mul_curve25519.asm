SECTION .text
	GLOBAL mul_curve25519
mul_curve25519:
sub rsp, 0x78 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x48 ], rbx; saving to stack
mov [ rsp + 0x50 ], rbp; saving to stack
mov [ rsp + 0x58 ], r12; saving to stack
mov [ rsp + 0x60 ], r13; saving to stack
mov [ rsp + 0x68 ], r14; saving to stack
mov [ rsp + 0x70 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, [ rax + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
imul rbx, [ rax + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r12, rbx; x20, x19<- arg1[1] * x10000
imul r13, [ rax + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
imul r14, [ rax + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r15, rcx, r13; x18, x17<- arg1[2] * x10001
mov rdx, r14; x10002 to rdx
mulx r14, r8, [ rsi + 0x18 ]; x14, x13<- arg1[3] * x10002
imul r9, [ rax + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
xchg rdx, r9; x10003, swapping with x10002, which is currently in rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rdx, rdi, [ rsi + 0x20 ]; x8, x7<- arg1[4] * x10003
add rdi, r8; could be done better, if r0 has been u8 as well
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdi, rcx
seto cl; spill OF x56 to reg (rcx)
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, r12
setc r12b; spill CF x52 to reg (r12)
clc;
adcx rdi, r11
movzx r12, r12b
lea r14, [ r14 + rdx ]
lea r14, [ r14 + r12 ]
movzx rcx, cl
lea r15, [ r15 + r14 ]
lea r15, [ r15 + rcx ]
adox rbp, r15
adcx r10, rbp
mov r11, rdi; x67, copying x63 here, cause x63 is needed in a reg for other than x67, namely all: , x67, x68, size: 2
shrd r11, r10, 51; x67 <- x65||x63 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r12, rcx, rbx; x16, x15<- arg1[2] * x10000
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r14, r15, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r10, [ rax + 0x0 ]; x40, x39<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x8 ], r14; spilling x48 to mem
mulx r8, r14, r13; x12, x11<- arg1[3] * x10001
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x10 ], rbp; spilling x40 to mem
mulx r9, rbp, r9; x6, x5<- arg1[4] * x10002
mov [ rsp + 0x18 ], r12; spilling x16 to mem
xor r12, r12
adox rbp, r14
adcx rbp, rcx
setc cl; spill CF x122 to reg (rcx)
clc;
adcx rbp, r10
setc r10b; spill CF x126 to reg (r10)
clc;
adcx rbp, r15
adox r8, r9
mov r15, -0x3 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox rbp, r11
movzx rcx, cl
lea r8, [ rcx + r8 ]
mov rcx, [ rsp + 0x18 ]
lea r8, [rcx+r8]
movzx r10, r10b
lea r8, [ r10 + r8 ]
mov r10, [ rsp + 0x10 ]
lea r8, [r10+r8]
adcx r8, [ rsp + 0x8 ]
adox r8, r12
mov r11, rbp; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x136, x137, size: 2
shrd r11, r8, 51; x136 <- x135||x133 >> 51
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r9, [ rax + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r10, [ rax + 0x10 ]; x46, x45<- arg1[0] * arg2[2]
mov rdx, rbx; x10000 to rdx
mulx rbx, r8, [ rsi + 0x18 ]; x10, x9<- arg1[3] * x10000
mov r12, rdx; preserving value of x10000 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mov [ rsp + 0x20 ], rcx; spilling x46 to mem
mulx r15, rcx, [ rsi + 0x10 ]; x32, x31<- arg1[2] * arg2[0]
mov rdx, r13; x10001 to rdx
mulx rdx, r13, [ rsi + 0x20 ]; x4, x3<- arg1[4] * x10001
test al, al
adox r13, r8
adcx r13, rcx
seto r8b; spill OF x102 to reg (r8)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r9
seto r9b; spill OF x110 to reg (r9)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, r10
setc r10b; spill CF x106 to reg (r10)
clc;
adcx r13, r11
movzx r8, r8b
lea rbx, [ rbx + rdx ]
lea rbx, [ rbx + r8 ]
movzx r10, r10b
lea r15, [ r15 + rbx ]
lea r15, [ r15 + r10 ]
movzx r9, r9b
lea r14, [ r14 + r15 ]
lea r14, [ r14 + r9 ]
adox r14, [ rsp + 0x20 ]
adc r14, 0x0
mov r11, r13; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x141, x142, size: 2
shrd r11, r14, 51; x141 <- x140||x138 >> 51
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r8, r12; x2, x1<- arg1[4] * x10000
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r10, r9, [ rsi + 0x0 ]; x44, x43<- arg1[0] * arg2[3]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, r15, [ rax + 0x8 ]; x30, x29<- arg1[2] * arg2[1]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r14, rcx, [ rsi + 0x8 ]; x36, x35<- arg1[1] * arg2[2]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x28 ], rdi; spilling x63 to mem
mov [ rsp + 0x30 ], r10; spilling x44 to mem
mulx rdi, r10, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
mov [ rsp + 0x38 ], r14; spilling x36 to mem
xor r14, r14
adox r8, r10
adcx r8, r15
setc r15b; spill CF x90 to reg (r15)
clc;
adcx r8, rcx
seto cl; spill OF x86 to reg (rcx)
mov r10, -0x3 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r9
setc r9b; spill CF x94 to reg (r9)
clc;
adcx r8, r11
movzx rcx, cl
lea rdi, [ rdi + r12 ]
lea rdi, [ rdi + rcx ]
movzx r15, r15b
lea rbx, [ rbx + rdi ]
lea rbx, [ rbx + r15 ]
movzx r9, r9b
lea rbx, [ r9 + rbx ]
mov r9, [ rsp + 0x38 ]
lea rbx, [r9+rbx]
adox rbx, [ rsp + 0x30 ]
adc rbx, 0x0
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r11, r12, [ rax + 0x8 ]; x24, x23<- arg1[3] * arg2[1]
mov rcx, r8; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x146, x147, size: 2
shrd rcx, rbx, 51; x146 <- x145||x143 >> 51
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdx, r15, [ rsi + 0x0 ]; x42, x41<- arg1[0] * arg2[4]
mov r9, rdx; preserving value of x42 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx rdi, rbx, [ rax + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r14, r10, [ rax + 0x0 ]; x22, x21<- arg1[4] * arg2[0]
mov [ rsp + 0x40 ], r9; spilling x42 to mem
xor r9, r9
adox r10, r12
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r9, [ rax + 0x18 ]; x34, x33<- arg1[1] * arg2[3]
adcx r10, rbx
setc bl; spill CF x74 to reg (rbx)
clc;
adcx r10, r9
setc r9b; spill CF x78 to reg (r9)
clc;
adcx r10, r15
setc r15b; spill CF x82 to reg (r15)
clc;
adcx r10, rcx
adox r11, r14
movzx rbx, bl
lea rdi, [ rdi + r11 ]
lea rdi, [ rdi + rbx ]
movzx r9, r9b
lea r12, [ r12 + rdi ]
lea r12, [ r12 + r9 ]
movzx r15, r15b
lea r12, [ r15 + r12 ]
mov r15, [ rsp + 0x40 ]
lea r12, [r15+r12]
adc r12, 0x0
mov rcx, 0x7ffffffffffff ; moving imm to reg
and r8, rcx; x147 <- x143&0x7ffffffffffff
mov r14, 0x33 ; moving imm to reg
bzhi r14, [ rsp + 0x28 ], r14; x68 <- x63 (only least 0x33 bits)
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbx + 0x18 ], r8; out1[3] = x147
mov r9, r10; x151, copying x148 here, cause x148 is needed in a reg for other than x151, namely all: , x151, x152, size: 2
shrd r9, r12, 51; x151 <- x150||x148 >> 51
imul r9, r9, 0x13; x153 <- x151 * 0x13
lea r14, [ r14 + r9 ]
and rbp, rcx; x137 <- x133&0x7ffffffffffff
mov r15, r14; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x155, x156, size: 2
shr r15, 51; x155 <- x154>> 51
lea r15, [ r15 + rbp ]
and r14, rcx; x156 <- x154&0x7ffffffffffff
mov r11, 0x33 ; moving imm to reg
bzhi r11, r15, r11; x159 <- x157 (only least 0x33 bits)
mov [ rbx + 0x0 ], r14; out1[0] = x156
mov rdi, 0x33 ; moving imm to reg
bzhi r10, r10, rdi; x152 <- x148 (only least 0x33 bits)
shr r15, 51; x158 <- x157>> 51
mov [ rbx + 0x20 ], r10; out1[4] = x152
bzhi r13, r13, rdi; x142 <- x138 (only least 0x33 bits)
lea r15, [ r15 + r13 ]
mov [ rbx + 0x10 ], r15; out1[2] = x160
mov [ rbx + 0x8 ], r11; out1[1] = x159
mov rbx, [ rsp + 0x48 ]; restoring from stack
mov rbp, [ rsp + 0x50 ]; restoring from stack
mov r12, [ rsp + 0x58 ]; restoring from stack
mov r13, [ rsp + 0x60 ]; restoring from stack
mov r14, [ rsp + 0x68 ]; restoring from stack
mov r15, [ rsp + 0x70 ]; restoring from stack
add rsp, 0x78 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 65.45, best 55.582608695652176, lastGood 58.75438596491228
; seed 775961493504765 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6045 ms / 500 runs=> 12.09ms/run
; Time spent for assembling and measureing (initial batch_size=114, initial num_batches=101): 1854 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.3066997518610422
; number reverted permutation/ tried permutation: 174 / 235 =74.043%
; number reverted decision/ tried decision: 168 / 266 =63.158%