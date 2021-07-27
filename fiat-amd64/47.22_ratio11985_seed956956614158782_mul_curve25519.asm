SECTION .text
	GLOBAL mul_curve25519
mul_curve25519:
sub rsp, 0x60 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x30 ], rbx; saving to stack
mov [ rsp + 0x38 ], rbp; saving to stack
mov [ rsp + 0x40 ], r12; saving to stack
mov [ rsp + 0x48 ], r13; saving to stack
mov [ rsp + 0x50 ], r14; saving to stack
mov [ rsp + 0x58 ], r15; saving to stack
imul rax, [ rdx + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
imul r10, [ rdx + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbx, rbp, r10; x20, x19<- arg1[1] * x10000
imul r12, [ r11 + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r14, r12; x14, x13<- arg1[3] * x10002
imul r15, [ r11 + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r15, rcx, r15; x8, x7<- arg1[4] * x10003
test al, al
adox rcx, r14
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r9, [ r11 + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r14, rdi, rax; x18, x17<- arg1[2] * x10001
adcx rcx, rdi
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x8 ], r10; spilling x10000 to mem
mulx rdi, r10, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
adox r13, r15
adcx r14, r13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, r15, r12; x6, x5<- arg1[4] * x10002
xor r13, r13
adox rcx, rbp
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx rbp, r13, [ rsi + 0x8 ]; x40, x39<- arg1[1] * arg2[0]
adox rbx, r14
adcx rcx, r9
adcx r8, rbx
mov r9, rcx; x67, copying x63 here, cause x63 is needed in a reg for other than x67, namely all: , x67, x68, size: 2
shrd r9, r8, 51; x67 <- x65||x63 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, rbx, [ rsp + 0x8 ]; x16, x15<- arg1[2] * x10000
mov rdx, rax; x10001 to rdx
mulx rax, r8, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x10001
add r15, r8; could be done better, if r0 has been u8 as well
adcx rax, r12
add r15, rbx; could be done better, if r0 has been u8 as well
adcx r14, rax
add r15, r13; could be done better, if r0 has been u8 as well
mov r12, rdx; preserving value of x10001 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx r13, rbx, [ rsi + 0x10 ]; x32, x31<- arg1[2] * arg2[0]
adcx rbp, r14
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mulx r8, rax, [ rsi + 0x0 ]; x46, x45<- arg1[0] * arg2[2]
add r15, r10; could be done better, if r0 has been u8 as well
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r10, r14, [ rsi + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
adcx rdi, rbp
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x10 ], r8; spilling x46 to mem
mulx rbp, r8, [ rsp + 0x8 ]; x10, x9<- arg1[3] * x10000
add r15, r9; could be done better, if r0 has been u8 as well
adc rdi, 0x0
mov r9, r15; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x137, x136, size: 2
shrd r9, rdi, 51; x136 <- x135||x133 >> 51
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r12, rdi, r12; x4, x3<- arg1[4] * x10001
add rdi, r8; could be done better, if r0 has been u8 as well
adcx rbp, r12
xor r8, r8
adox rdi, rbx
adox r13, rbp
adcx rdi, r14
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx rbx, r14, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
adcx r10, r13
add rdi, rax; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, r12, [ r11 + 0x18 ]; x44, x43<- arg1[0] * arg2[3]
add rdi, r9; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, rbp, [ r11 + 0x8 ]; x30, x29<- arg1[2] * arg2[1]
adc r10, 0x0
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mulx r13, r8, [ rsi + 0x8 ]; x36, x35<- arg1[1] * arg2[2]
mov [ rsp + 0x18 ], rax; spilling x44 to mem
mov rax, rdi; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x142, x141, size: 2
shrd rax, r10, 51; x141 <- x140||x138 >> 51
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x20 ], rax; spilling x141 to mem
mulx r10, rax, [ rsp + 0x8 ]; x2, x1<- arg1[4] * x10000
add rax, r14; could be done better, if r0 has been u8 as well
adcx rbx, r10
add rax, rbp; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r14, rbp, [ r11 + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r8
adcx r9, rbx
adox r13, r9
add rax, r12; could be done better, if r0 has been u8 as well
adcx r13, [ rsp + 0x18 ]
add rax, [ rsp + 0x20 ]; could be done better, if r0 has been u8 as well
adc r13, 0x0
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r8, [ r11 + 0x20 ]; x42, x41<- arg1[0] * arg2[4]
mov rbx, rax; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x146, x147, size: 2
shrd rbx, r13, 51; x146 <- x145||x143 >> 51
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx r9, r13, [ rsi + 0x20 ]; x22, x21<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x28 ], rcx; spilling x63 to mem
mulx r10, rcx, [ r11 + 0x8 ]; x24, x23<- arg1[3] * arg2[1]
add r13, rcx; could be done better, if r0 has been u8 as well
adcx r10, r9
xor r9, r9
adox r13, rbp
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mulx rbp, rcx, [ rsi + 0x8 ]; x34, x33<- arg1[1] * arg2[3]
adcx r13, rcx
adox r14, r10
adcx rbp, r14
xor r10, r10
adox r13, r8
adcx r13, rbx
adox r12, rbp
adc r12, 0x0
mov r9, 0x33 ; moving imm to reg
bzhi r9, r13, r9; x152 <- x148 (only least 0x33 bits)
shrd r13, r12, 51; x151 <- x150||x148 >> 51
imul r13, r13, 0x13; x153 <- x151 * 0x13
mov r8, 0x33 ; moving imm to reg
bzhi r8, [ rsp + 0x28 ], r8; x68 <- x63 (only least 0x33 bits)
lea r8, [ r8 + r13 ]
mov rbx, 0x33 ; moving imm to reg
bzhi r15, r15, rbx; x137 <- x133 (only least 0x33 bits)
mov rcx, r8; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x156, x155, size: 2
shr rcx, 51; x155 <- x154>> 51
lea rcx, [ rcx + r15 ]
bzhi rdi, rdi, rbx; x142 <- x138 (only least 0x33 bits)
bzhi rax, rax, rbx; x147 <- x143 (only least 0x33 bits)
mov r14, rcx; x158, copying x157 here, cause x157 is needed in a reg for other than x158, namely all: , x159, x158, size: 2
shr r14, 51; x158 <- x157>> 51
mov rbp, 0x7ffffffffffff ; moving imm to reg
and rcx, rbp; x159 <- x157&0x7ffffffffffff
lea r14, [ r14 + rdi ]
and r8, rbp; x156 <- x154&0x7ffffffffffff
mov r12, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r12 + 0x8 ], rcx; out1[1] = x159
mov [ r12 + 0x0 ], r8; out1[0] = x156
mov [ r12 + 0x10 ], r14; out1[2] = x160
mov [ r12 + 0x18 ], rax; out1[3] = x147
mov [ r12 + 0x20 ], r9; out1[4] = x152
mov rbx, [ rsp + 0x30 ]; restoring from stack
mov rbp, [ rsp + 0x38 ]; restoring from stack
mov r12, [ rsp + 0x40 ]; restoring from stack
mov r13, [ rsp + 0x48 ]; restoring from stack
mov r14, [ rsp + 0x50 ]; restoring from stack
mov r15, [ rsp + 0x58 ]; restoring from stack
add rsp, 0x60 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 70.29, best 43.77401129943503, lastGood 47.224242424242426
; seed 956956614158782 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 854095 ms / 60000 runs=> 14.234916666666667ms/run
; Time spent for assembling and measureing (initial batch_size=165, initial num_batches=101): 320925 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.3757485993946809
; number reverted permutation/ tried permutation: 25733 / 29945 =85.934%
; number reverted decision/ tried decision: 20458 / 30056 =68.066%