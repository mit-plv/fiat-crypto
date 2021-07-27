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
imul rax, [ rdx + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
imul r10, [ rdx + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
imul r11, [ rdx + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
mov rbx, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rbp, r12, [ rbx + 0x0 ]; x40, x39<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rax, r13, rax; x8, x7<- arg1[4] * x10003
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r14, r15, r10; x14, x13<- arg1[3] * x10002
imul rcx, [ rbx + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, r8, r10; x6, x5<- arg1[4] * x10002
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mulx r9, rdi, r11; x18, x17<- arg1[2] * x10001
mov rdx, rcx; x10000 to rdx
mov [ rsp + 0x8 ], rbp; spilling x40 to mem
mulx rcx, rbp, [ rsi + 0x8 ]; x20, x19<- arg1[1] * x10000
add r13, r15; could be done better, if r0 has been u8 as well
adcx r14, rax
mulx rax, r15, [ rsi + 0x10 ]; x16, x15<- arg1[2] * x10000
mov [ rsp + 0x10 ], r12; spilling x39 to mem
xor r12, r12
adox r13, rdi
adox r9, r14
adcx r13, rbp
adcx rcx, r9
mov rdi, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbp, r14, [ rbx + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r12, [ rbx + 0x8 ]; x48, x47<- arg1[0] * arg2[1]
add r13, r14; could be done better, if r0 has been u8 as well
adcx rbp, rcx
mov rcx, r13; x67, copying x63 here, cause x63 is needed in a reg for other than x67, namely all: , x67, x68, size: 2
shrd rcx, rbp, 51; x67 <- x65||x63 >> 51
mov rdx, r11; x10001 to rdx
mulx r11, r14, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x10001
add r8, r14; could be done better, if r0 has been u8 as well
adcx r11, r10
add r8, r15; could be done better, if r0 has been u8 as well
mulx rdx, r10, [ rsi + 0x20 ]; x4, x3<- arg1[4] * x10001
adcx rax, r11
xor r15, r15
adox r8, [ rsp + 0x10 ]
adcx r8, r12
mov r12, rdx; preserving value of x4 into a new reg
mov rdx, [ rbx + 0x10 ]; saving arg2[2] in rdx.
mulx rbp, r14, [ rsi + 0x0 ]; x46, x45<- arg1[0] * arg2[2]
adox rax, [ rsp + 0x8 ]
adcx r9, rax
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r11, rax, rdi; x10, x9<- arg1[3] * x10000
add r10, rax; could be done better, if r0 has been u8 as well
adcx r11, r12
xor r12, r12
adox r8, rcx
adox r9, r12
mov rdx, [ rbx + 0x8 ]; arg2[1] to rdx
mulx r15, rcx, [ rsi + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r12, [ rbx + 0x0 ]; x32, x31<- arg1[2] * arg2[0]
adcx r10, r12
adcx rax, r11
add r10, rcx; could be done better, if r0 has been u8 as well
adcx r15, rax
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r11, rcx, [ rbx + 0x8 ]; x30, x29<- arg1[2] * arg2[1]
mov r12, r8; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x137, x136, size: 2
shrd r12, r9, 51; x136 <- x135||x133 >> 51
xor r9, r9
adox r10, r14
adcx r10, r12
adox rbp, r15
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rdi, r14, rdi; x2, x1<- arg1[4] * x10000
adc rbp, 0x0
mov rdx, [ rbx + 0x10 ]; arg2[2] to rdx
mulx rax, r15, [ rsi + 0x8 ]; x36, x35<- arg1[1] * arg2[2]
mov r12, r10; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x142, x141, size: 2
shrd r12, rbp, 51; x141 <- x140||x138 >> 51
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mulx rbp, r9, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
add r14, r9; could be done better, if r0 has been u8 as well
adcx rbp, rdi
add r14, rcx; could be done better, if r0 has been u8 as well
adcx r11, rbp
xor rcx, rcx
adox r14, r15
mov rdx, [ rbx + 0x0 ]; arg2[0] to rdx
mulx rdi, r15, [ rsi + 0x20 ]; x22, x21<- arg1[4] * arg2[0]
adox rax, r11
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, rbp, [ rbx + 0x18 ]; x44, x43<- arg1[0] * arg2[3]
adcx r14, rbp
adcx r9, rax
add r14, r12; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r12, r11, [ rbx + 0x8 ]; x24, x23<- arg1[3] * arg2[1]
adc r9, 0x0
mov rax, r14; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd rax, r9, 51; x146 <- x145||x143 >> 51
xor rbp, rbp
adox r15, r11
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r11, [ rbx + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
adcx r15, r11
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r11, [ rbx + 0x20 ]; x42, x41<- arg1[0] * arg2[4]
adox r12, rdi
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, rbp, [ rbx + 0x18 ]; x34, x33<- arg1[1] * arg2[3]
adcx rcx, r12
xor r12, r12
adox r15, rbp
adcx r15, r11
adox rdi, rcx
adcx r9, rdi
test al, al
adox r15, rax
adox r9, r12
mov rax, r15; x151, copying x148 here, cause x148 is needed in a reg for other than x151, namely all: , x151, x152, size: 2
shrd rax, r9, 51; x151 <- x150||x148 >> 51
mov r11, 0x33 ; moving imm to reg
bzhi r10, r10, r11; x142 <- x138 (only least 0x33 bits)
mov rbp, 0x7ffffffffffff ; moving imm to reg
and r8, rbp; x137 <- x133&0x7ffffffffffff
imul rax, rax, 0x13; x153 <- x151 * 0x13
and r13, rbp; x68 <- x63&0x7ffffffffffff
lea r13, [ r13 + rax ]
bzhi r11, r13, r11; x156 <- x154 (only least 0x33 bits)
shr r13, 51; x155 <- x154>> 51
and r15, rbp; x152 <- x148&0x7ffffffffffff
lea r13, [ r13 + r8 ]
mov rcx, r13; x159, copying x157 here, cause x157 is needed in a reg for other than x159, namely all: , x159, x158, size: 2
and rcx, rbp; x159 <- x157&0x7ffffffffffff
mov rdi, 0x33 ; moving imm to reg
bzhi r14, r14, rdi; x147 <- x143 (only least 0x33 bits)
mov r9, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ r9 + 0x0 ], r11; out1[0] = x156
mov [ r9 + 0x20 ], r15; out1[4] = x152
mov [ r9 + 0x18 ], r14; out1[3] = x147
shr r13, 51; x158 <- x157>> 51
mov [ r9 + 0x8 ], rcx; out1[1] = x159
lea r13, [ r13 + r10 ]
mov [ r9 + 0x10 ], r13; out1[2] = x160
mov rbx, [ rsp + 0x18 ]; restoring from stack
mov rbp, [ rsp + 0x20 ]; restoring from stack
mov r12, [ rsp + 0x28 ]; restoring from stack
mov r13, [ rsp + 0x30 ]; restoring from stack
mov r14, [ rsp + 0x38 ]; restoring from stack
mov r15, [ rsp + 0x40 ]; restoring from stack
add rsp, 0x48 
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; clocked at 4765 MHz
; first cyclecount 67.295, best 44.36024844720497, lastGood 45.424050632911396
; seed 212576899785283 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 545057 ms / 60000 runs=> 9.084283333333333ms/run
; Time spent for assembling and measureing (initial batch_size=157, initial num_batches=101): 162866 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.2988054460359192
; number reverted permutation/ tried permutation: 23990 / 29854 =80.358%
; number reverted decision/ tried decision: 19910 / 30147 =66.043%