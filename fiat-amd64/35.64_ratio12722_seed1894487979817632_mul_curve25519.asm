SECTION .text
	GLOBAL mul_curve25519
mul_curve25519:
sub rsp, 0x68 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x38 ], rbx; saving to stack
mov [ rsp + 0x40 ], rbp; saving to stack
mov [ rsp + 0x48 ], r12; saving to stack
mov [ rsp + 0x50 ], r13; saving to stack
mov [ rsp + 0x58 ], r14; saving to stack
mov [ rsp + 0x60 ], r15; saving to stack
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, [ rax + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
imul rbx, [ rax + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
imul rbp, [ rax + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
imul r12, [ rax + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r13, r14, r12; x14, x13<- arg1[3] * x10002
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx rbx, r15, rbx; x8, x7<- arg1[4] * x10003
imul rcx, [ rax + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r9, rbp; x18, x17<- arg1[2] * x10001
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov [ rsp + 0x8 ], r10; spilling x50 to mem
mulx rdi, r10, rcx; x20, x19<- arg1[1] * x10000
test al, al
adox r15, r14
adox r13, rbx
adcx r15, r9
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, r10
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r9, rbp; x12, x11<- arg1[3] * x10001
adcx r8, r13
clc;
adcx r15, r11
mov rdx, rbp; x10001 to rdx
mulx rdx, rbp, [ rsi + 0x20 ]; x4, x3<- arg1[4] * x10001
xchg rdx, r12; x10002, swapping with x4, which is currently in rdx
mulx rdx, r11, [ rsi + 0x20 ]; x6, x5<- arg1[4] * x10002
mov r10, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r13, r14, rcx; x16, x15<- arg1[2] * x10000
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x10 ], r12; spilling x4 to mem
mov [ rsp + 0x18 ], rbp; spilling x3 to mem
mulx r12, rbp, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
adox rdi, r8
adcx rdi, [ rsp + 0x8 ]
add r11, r9; could be done better, if r0 has been u8 as well
mov r9, 0x7ffffffffffff ; moving imm to reg
setc r8b; spill CF x118 to reg (r8)
mov [ rsp + 0x20 ], r12; spilling x48 to mem
mov r12, r15; x68, copying x63 here, cause x63 is needed in a reg for other than x68, namely all: , x68, x67, size: 2
and r12, r9; x68 <- x63&0x7ffffffffffff
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x28 ], r12; spilling x68 to mem
mulx r9, r12, [ rsi + 0x8 ]; x40, x39<- arg1[1] * arg2[0]
shrd r15, rdi, 51; x67 <- x65||x63 >> 51
xor rdi, rdi
adox r11, r14
mov rdx, rcx; x10000 to rdx
mulx rcx, r14, [ rsi + 0x18 ]; x10, x9<- arg1[3] * x10000
movzx r8, r8b
lea rbx, [ rbx + r10 ]
lea rbx, [ rbx + r8 ]
adox r13, rbx
adcx r11, r12
adcx r9, r13
mov r10, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r8, r12, [ rax + 0x0 ]; x32, x31<- arg1[2] * arg2[0]
test al, al
adox r14, [ rsp + 0x18 ]
adcx r11, rbp
adcx r9, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, rbx, [ rax + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
adox rcx, [ rsp + 0x10 ]
add r11, r15; could be done better, if r0 has been u8 as well
adc r9, 0x0
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx r15, r13, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
mov rdi, r11; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x137, x136, size: 2
shrd rdi, r9, 51; x136 <- x135||x133 >> 51
xor r9, r9
adox r14, r12
adox r8, rcx
adcx r14, rbx
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r12, rbx, [ rsi + 0x0 ]; x46, x45<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mulx r10, rcx, r10; x2, x1<- arg1[4] * x10000
adcx rbp, r8
xor r8, r8
adox r14, rbx
adox r12, rbp
adcx r14, rdi
adc r12, 0x0
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r9, rdi, [ rsi + 0x8 ]; x36, x35<- arg1[1] * arg2[2]
xor rbx, rbx
adox rcx, r13
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r13, [ rax + 0x8 ]; x30, x29<- arg1[2] * arg2[1]
adox r15, r10
adcx rcx, r13
adcx r8, r15
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mulx rdx, r10, [ rsi + 0x0 ]; x42, x41<- arg1[0] * arg2[4]
mov rbp, rdx; preserving value of x42 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r13, r15, [ rax + 0x18 ]; x44, x43<- arg1[0] * arg2[3]
mov rbx, r14; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x142, x141, size: 2
shrd rbx, r12, 51; x141 <- x140||x138 >> 51
xor r12, r12
adox rcx, rdi
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mulx rdi, r12, [ rsi + 0x20 ]; x22, x21<- arg1[4] * arg2[0]
adox r9, r8
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x30 ], rbp; spilling x42 to mem
mulx r8, rbp, [ rax + 0x18 ]; x34, x33<- arg1[1] * arg2[3]
adcx rcx, r15
adcx r13, r9
xor r15, r15
adox rcx, rbx
adox r13, r15
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r9, [ rax + 0x8 ]; x24, x23<- arg1[3] * arg2[1]
adcx r12, r9
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mulx r9, r15, [ rsi + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
adcx rbx, rdi
xor rdi, rdi
adox r12, r15
seto r15b; spill OF x74 to reg (r15)
mov rdi, rcx; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x147, x146, size: 2
shrd rdi, r13, 51; x146 <- x145||x143 >> 51
sar  r15b, 1
adcx r9, rbx
adox r12, rbp
clc;
adcx r12, r10
adox r8, r9
adcx r8, [ rsp + 0x30 ]
xor r10, r10
adox r12, rdi
adox r8, r10
mov rbp, 0x33 ; moving imm to reg
bzhi rcx, rcx, rbp; x147 <- x143 (only least 0x33 bits)
mov r13, r12; x151, copying x148 here, cause x148 is needed in a reg for other than x151, namely all: , x151, x152, size: 2
shrd r13, r8, 51; x151 <- x150||x148 >> 51
imul r13, r13, 0x13; x153 <- x151 * 0x13
add r13, [ rsp + 0x28 ]
mov rbx, r13; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x155, x156, size: 2
shr rbx, 51; x155 <- x154>> 51
bzhi r11, r11, rbp; x137 <- x133 (only least 0x33 bits)
mov r15, 0x7ffffffffffff ; moving imm to reg
and r14, r15; x142 <- x138&0x7ffffffffffff
bzhi r13, r13, rbp; x156 <- x154 (only least 0x33 bits)
mov rdi, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rdi + 0x18 ], rcx; out1[3] = x147
lea rbx, [ rbx + r11 ]
mov [ rdi + 0x0 ], r13; out1[0] = x156
mov r9, rbx; x158, copying x157 here, cause x157 is needed in a reg for other than x158, namely all: , x158, x159, size: 2
shr r9, 51; x158 <- x157>> 51
lea r9, [ r9 + r14 ]
and rbx, r15; x159 <- x157&0x7ffffffffffff
and r12, r15; x152 <- x148&0x7ffffffffffff
mov [ rdi + 0x20 ], r12; out1[4] = x152
mov [ rdi + 0x10 ], r9; out1[2] = x160
mov [ rdi + 0x8 ], rbx; out1[1] = x159
mov rbx, [ rsp + 0x38 ]; restoring from stack
mov rbp, [ rsp + 0x40 ]; restoring from stack
mov r12, [ rsp + 0x48 ]; restoring from stack
mov r13, [ rsp + 0x50 ]; restoring from stack
mov r14, [ rsp + 0x58 ]; restoring from stack
mov r15, [ rsp + 0x60 ]; restoring from stack
add rsp, 0x68 
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; clocked at 3600 MHz
; first cyclecount 42.55, best 34.67906976744186, lastGood 35.64383561643836
; seed 1894487979817632 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 537886 ms / 60000 runs=> 8.964766666666666ms/run
; Time spent for assembling and measureing (initial batch_size=219, initial num_batches=101): 237446 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.44144298234198326
; number reverted permutation/ tried permutation: 23284 / 30109 =77.332%
; number reverted decision/ tried decision: 20424 / 29892 =68.326%