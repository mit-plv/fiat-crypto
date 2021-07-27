SECTION .text
	GLOBAL mul_curve25519
mul_curve25519:
sub rsp, 0x58 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x28 ], rbx; saving to stack
mov [ rsp + 0x30 ], rbp; saving to stack
mov [ rsp + 0x38 ], r12; saving to stack
mov [ rsp + 0x40 ], r13; saving to stack
mov [ rsp + 0x48 ], r14; saving to stack
mov [ rsp + 0x50 ], r15; saving to stack
imul rax, [ rdx + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
mov r10, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r11, rbx, rax; x20, x19<- arg1[1] * x10000
imul rbp, [ r10 + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
imul r12, [ r10 + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r13, r12; x8, x7<- arg1[4] * x10003
imul r14, [ r10 + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, rcx, rbp; x14, x13<- arg1[3] * x10002
test al, al
adox r13, rcx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r9, [ r10 + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
mov rdx, r14; x10001 to rdx
mulx r14, rcx, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x10001
adox r15, r12
adcx r13, rcx
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, rbx
setc bl; spill CF x56 to reg (rbx)
clc;
adcx r13, r9
mov r9, 0x33 ; moving imm to reg
setc cl; spill CF x64 to reg (rcx)
seto r12b; spill OF x60 to reg (r12)
bzhi r9, r13, r9; x68 <- x63 (only least 0x33 bits)
sar  bl, 1
adcx r14, r15
mov r15, rdx; preserving value of x10001 into a new reg
mov rdx, [ r10 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx rbx, rdi, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
mov rdx, r15; x10001 to rdx
mov [ rsp + 0x8 ], r9; spilling x68 to mem
mulx r15, r9, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x10001
sar  r12b, 1
adcx r11, r14
sar  cl, 1
adcx r8, r11
mov r12, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbp, rcx, rbp; x6, x5<- arg1[4] * x10002
shrd r13, r8, 51; x67 <- x65||x63 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, r11, rax; x16, x15<- arg1[2] * x10000
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x10 ], r13; spilling x67 to mem
mulx r8, r13, [ r10 + 0x0 ]; x40, x39<- arg1[1] * arg2[0]
add rcx, r9; could be done better, if r0 has been u8 as well
adcx r15, rbp
add rcx, r11; could be done better, if r0 has been u8 as well
adcx r14, r15
add rcx, r13; could be done better, if r0 has been u8 as well
adcx r8, r14
add rcx, rdi; could be done better, if r0 has been u8 as well
adcx rbx, r8
add rcx, [ rsp + 0x10 ]; could be done better, if r0 has been u8 as well
adc rbx, 0x0
mov rdx, [ r10 + 0x0 ]; arg2[0] to rdx
mulx rdi, r9, [ rsi + 0x10 ]; x32, x31<- arg1[2] * arg2[0]
mov rdx, [ r10 + 0x8 ]; arg2[1] to rdx
mulx rbp, r11, [ rsi + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
mov r13, rcx; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x136, x137, size: 2
shrd r13, rbx, 51; x136 <- x135||x133 >> 51
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r15, r14, rax; x10, x9<- arg1[3] * x10000
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, rbx, [ r10 + 0x10 ]; x46, x45<- arg1[0] * arg2[2]
mov rdx, r12; x10001 to rdx
mulx rdx, r12, [ rsi + 0x20 ]; x4, x3<- arg1[4] * x10001
test al, al
adox r12, r14
adcx r12, r9
adox r15, rdx
adcx rdi, r15
xor r9, r9
adox r12, r11
adox rbp, rdi
adcx r12, rbx
adcx r8, rbp
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rax, r11, rax; x2, x1<- arg1[4] * x10000
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r14, rbx, [ rsi + 0x0 ]; x44, x43<- arg1[0] * arg2[3]
add r12, r13; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r15, [ r10 + 0x0 ]; x26, x25<- arg1[3] * arg2[0]
adc r8, 0x0
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, rbp, [ r10 + 0x8 ]; x30, x29<- arg1[2] * arg2[1]
mov r9, r12; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x141, x142, size: 2
shrd r9, r8, 51; x141 <- x140||x138 >> 51
add r11, r15; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, r8, [ r10 + 0x10 ]; x36, x35<- arg1[1] * arg2[2]
adcx r13, rax
xor rax, rax
adox r11, rbp
mov rdx, [ r10 + 0x20 ]; arg2[4] to rdx
mulx rdx, rbp, [ rsi + 0x0 ]; x42, x41<- arg1[0] * arg2[4]
adox rdi, r13
adcx r11, r8
adcx r15, rdi
xor r8, r8
adox r11, rbx
mov rax, rdx; preserving value of x42 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbx, r13, [ r10 + 0x0 ]; x22, x21<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rdi, r8, [ r10 + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
adcx r11, r9
adox r14, r15
mov rdx, [ r10 + 0x18 ]; arg2[3] to rdx
mulx r9, r15, [ rsi + 0x8 ]; x34, x33<- arg1[1] * arg2[3]
adc r14, 0x0
mov [ rsp + 0x18 ], rax; spilling x42 to mem
mov rax, r11; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd rax, r14, 51; x146 <- x145||x143 >> 51
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x20 ], rax; spilling x146 to mem
mulx r14, rax, [ r10 + 0x8 ]; x24, x23<- arg1[3] * arg2[1]
add r13, rax; could be done better, if r0 has been u8 as well
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r13, r8
adcx r14, rbx
clc;
adcx r13, r15
adox rdi, r14
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r13, rbp
adcx r9, rdi
clc;
adcx r13, [ rsp + 0x20 ]
adox r9, [ rsp + 0x18 ]
adc r9, 0x0
mov rbp, 0x7ffffffffffff ; moving imm to reg
and r12, rbp; x142 <- x138&0x7ffffffffffff
mov rbx, r13; x151, copying x148 here, cause x148 is needed in a reg for other than x151, namely all: , x151, x152, size: 2
shrd rbx, r9, 51; x151 <- x150||x148 >> 51
imul rbx, rbx, 0x13; x153 <- x151 * 0x13
and rcx, rbp; x137 <- x133&0x7ffffffffffff
add rbx, [ rsp + 0x8 ]
mov r8, rbx; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x155, x156, size: 2
shr r8, 51; x155 <- x154>> 51
and rbx, rbp; x156 <- x154&0x7ffffffffffff
lea r8, [ r8 + rcx ]
mov r15, r8; x159, copying x157 here, cause x157 is needed in a reg for other than x159, namely all: , x158, x159, size: 2
and r15, rbp; x159 <- x157&0x7ffffffffffff
and r13, rbp; x152 <- x148&0x7ffffffffffff
mov r14, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r14 + 0x8 ], r15; out1[1] = x159
shr r8, 51; x158 <- x157>> 51
and r11, rbp; x147 <- x143&0x7ffffffffffff
mov [ r14 + 0x18 ], r11; out1[3] = x147
lea r8, [ r8 + r12 ]
mov [ r14 + 0x0 ], rbx; out1[0] = x156
mov [ r14 + 0x20 ], r13; out1[4] = x152
mov [ r14 + 0x10 ], r8; out1[2] = x160
mov rbx, [ rsp + 0x28 ]; restoring from stack
mov rbp, [ rsp + 0x30 ]; restoring from stack
mov r12, [ rsp + 0x38 ]; restoring from stack
mov r13, [ rsp + 0x40 ]; restoring from stack
mov r14, [ rsp + 0x48 ]; restoring from stack
mov r15, [ rsp + 0x50 ]; restoring from stack
add rsp, 0x58 
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; clocked at 1600 MHz
; first cyclecount 33.315, best 27.235690235690235, lastGood 27.256756756756758
; seed 3644061545824544 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1056733 ms / 60000 runs=> 17.612216666666665ms/run
; Time spent for assembling and measureing (initial batch_size=296, initial num_batches=101): 570090 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.5394834835289519
; number reverted permutation/ tried permutation: 27512 / 30167 =91.199%
; number reverted decision/ tried decision: 20824 / 29834 =69.800%