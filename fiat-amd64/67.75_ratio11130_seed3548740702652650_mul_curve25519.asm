SECTION .text
	GLOBAL mul_curve25519
mul_curve25519:
sub rsp, 0x48 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x18 ], rbx; saving to stack
mov [ rsp + 0x20 ], rbp; saving to stack
mov [ rsp + 0x28 ], r12; saving to stack
mov [ rsp + 0x30 ], r13; saving to stack
mov [ rsp + 0x38 ], r14; saving to stack
mov [ rsp + 0x40 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, [ rax + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
imul rbx, [ rax + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
imul rbp, [ rax + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
imul r12, [ rax + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
imul r13, [ rax + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
mov rdx, rbx; x10003 to rdx
mulx rdx, rbx, [ rsi + 0x20 ]; x8, x7<- arg1[4] * x10003
xchg rdx, rbp; x10002, swapping with x8, which is currently in rdx
mulx r14, r15, [ rsi + 0x18 ]; x14, x13<- arg1[3] * x10002
test al, al
adox rbx, r15
mov rcx, rdx; preserving value of x10002 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r8, r9, r13; x18, x17<- arg1[2] * x10001
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r15, rdi, r12; x20, x19<- arg1[1] * x10000
adcx rbx, r9
adox r14, rbp
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbx, rdi
adcx r8, r14
clc;
adcx rbx, r11
adox r15, r8
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r11, r9, [ rsi + 0x8 ]; x40, x39<- arg1[1] * arg2[0]
adcx r10, r15
mov rdx, rcx; x10002 to rdx
mulx rdx, rcx, [ rsi + 0x20 ]; x6, x5<- arg1[4] * x10002
mov rdi, rdx; preserving value of x6 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx r14, r8, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
mov r15, rbx; x67, copying x63 here, cause x63 is needed in a reg for other than x67, namely all: , x68, x67, size: 2
shrd r15, r10, 51; x67 <- x65||x63 >> 51
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, rbp, r13; x12, x11<- arg1[3] * x10001
test al, al
adox rcx, rbp
adox r10, rdi
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, rbp, r12; x16, x15<- arg1[2] * x10000
adcx rcx, rbp
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, r9
adcx rdi, r10
adox r11, rdi
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r9, r10, r12; x10, x9<- arg1[3] * x10000
add rcx, r8; could be done better, if r0 has been u8 as well
adcx r14, r11
test al, al
adox rcx, r15
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r13, r8, r13; x4, x3<- arg1[4] * x10001
mov r15, 0x0 ; moving imm to reg
adox r14, r15
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r11, [ rsi + 0x10 ]; x32, x31<- arg1[2] * arg2[0]
adcx r8, r10
adcx r9, r13
mov r10, rcx; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x136, x137, size: 2
shrd r10, r14, 51; x136 <- x135||x133 >> 51
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx r13, r14, [ rsi + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
xor rbp, rbp
adox r8, r11
adox rdi, r9
adcx r8, r14
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r15, r11, [ rsi + 0x0 ]; x46, x45<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r14, [ rax + 0x18 ]; x44, x43<- arg1[0] * arg2[3]
mov [ rsp + 0x8 ], r9; spilling x44 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r8, r11
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r11, r12; x2, x1<- arg1[4] * x10000
adcx r13, rdi
adox r15, r13
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r13, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
xor r9, r9
adox r8, r10
adox r15, r9
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mulx rbp, r10, [ rsi + 0x10 ]; x30, x29<- arg1[2] * arg2[1]
mov r9, r8; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x141, x142, size: 2
shrd r9, r15, 51; x141 <- x140||x138 >> 51
add r11, r13; could be done better, if r0 has been u8 as well
adcx rdi, r12
add r11, r10; could be done better, if r0 has been u8 as well
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r12, r13, [ rsi + 0x8 ]; x36, x35<- arg1[1] * arg2[2]
adcx rbp, rdi
xor r15, r15
adox r11, r13
adox r12, rbp
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mulx r10, rdi, [ rsi + 0x8 ]; x34, x33<- arg1[1] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdx, r13, [ rsi + 0x0 ]; x42, x41<- arg1[0] * arg2[4]
adcx r11, r14
mov r14, -0x3 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r11, r9
mov r9, rdx; preserving value of x42 into a new reg
mov rdx, [ rax + 0x0 ]; saving arg2[0] in rdx.
mulx rbp, r15, [ rsi + 0x20 ]; x22, x21<- arg1[4] * arg2[0]
adcx r12, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x10 ], rbx; spilling x63 to mem
mulx r14, rbx, [ rax + 0x8 ]; x24, x23<- arg1[3] * arg2[1]
clc;
adcx r15, rbx
adcx r14, rbp
mov rbp, 0x0 ; moving imm to reg
adox r12, rbp
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, rbp, [ rax + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
add r15, rbp; could be done better, if r0 has been u8 as well
adcx rbx, r14
xor r14, r14
adox r15, rdi
adox r10, rbx
mov rdi, r11; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd rdi, r12, 51; x146 <- x145||x143 >> 51
xor r12, r12
adox r15, r13
adox r9, r10
adcx r15, rdi
adc r9, 0x0
mov r14, 0x7ffffffffffff ; moving imm to reg
and r8, r14; x142 <- x138&0x7ffffffffffff
mov r13, [ rsp + 0x10 ]; x68, copying x63 here, cause x63 is needed in a reg for other than x68, namely all: , x68, size: 1
and r13, r14; x68 <- x63&0x7ffffffffffff
mov rbp, r15; x152, copying x148 here, cause x148 is needed in a reg for other than x152, namely all: , x151, x152, size: 2
and rbp, r14; x152 <- x148&0x7ffffffffffff
shrd r15, r9, 51; x151 <- x150||x148 >> 51
imul r15, r15, 0x13; x153 <- x151 * 0x13
mov rbx, 0x33 ; moving imm to reg
bzhi rcx, rcx, rbx; x137 <- x133 (only least 0x33 bits)
mov r10, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r10 + 0x20 ], rbp; out1[4] = x152
lea r13, [ r13 + r15 ]
mov rdi, r13; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x156, x155, size: 2
shr rdi, 51; x155 <- x154>> 51
lea rdi, [ rdi + rcx ]
bzhi r13, r13, rbx; x156 <- x154 (only least 0x33 bits)
mov r9, rdi; x158, copying x157 here, cause x157 is needed in a reg for other than x158, namely all: , x158, x159, size: 2
shr r9, 51; x158 <- x157>> 51
mov [ r10 + 0x0 ], r13; out1[0] = x156
bzhi r11, r11, rbx; x147 <- x143 (only least 0x33 bits)
lea r9, [ r9 + r8 ]
bzhi rdi, rdi, rbx; x159 <- x157 (only least 0x33 bits)
mov [ r10 + 0x10 ], r9; out1[2] = x160
mov [ r10 + 0x18 ], r11; out1[3] = x147
mov [ r10 + 0x8 ], rdi; out1[1] = x159
mov rbx, [ rsp + 0x18 ]; restoring from stack
mov rbp, [ rsp + 0x20 ]; restoring from stack
mov r12, [ rsp + 0x28 ]; restoring from stack
mov r13, [ rsp + 0x30 ]; restoring from stack
mov r14, [ rsp + 0x38 ]; restoring from stack
mov r15, [ rsp + 0x40 ]; restoring from stack
add rsp, 0x48 
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; clocked at 3000 MHz
; first cyclecount 91.2, best 66.86821705426357, lastGood 67.75193798449612
; seed 3548740702652650 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 858457 ms / 60000 runs=> 14.307616666666666ms/run
; Time spent for assembling and measureing (initial batch_size=126, initial num_batches=101): 352412 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.41051794091026106
; number reverted permutation/ tried permutation: 25193 / 30093 =83.717%
; number reverted decision/ tried decision: 19539 / 29908 =65.330%