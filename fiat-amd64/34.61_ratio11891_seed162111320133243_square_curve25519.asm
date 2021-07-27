SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x30 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x0 ], rbx; saving to stack
mov [ rsp + 0x8 ], rbp; saving to stack
mov [ rsp + 0x10 ], r12; saving to stack
mov [ rsp + 0x18 ], r13; saving to stack
mov [ rsp + 0x20 ], r14; saving to stack
mov [ rsp + 0x28 ], r15; saving to stack
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, r10, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
imul r11, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
imul rbx, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
imul rbp, r11, 0x2; x2 <- x1 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r12, r13, rbp; x22, x21<- arg1[1] * x2
imul r14, rbx, 0x2; x5 <- x4 * 0x2
mov rdx, r14; x5 to rdx
mulx rdx, r14, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x5
test al, al
adox r14, r13
adox r12, rdx
adcx r14, r10
adcx rax, r12
imul r15, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mov rcx, r14; x47, copying x43 here, cause x43 is needed in a reg for other than x47, namely all: , x47, x48, size: 2
shrd rcx, rax, 51; x47 <- x45||x43 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, r9, rbp; x16, x15<- arg1[2] * x2
mov rdx, r15; x8 to rdx
mulx rdx, r15, [ rsi + 0x0 ]; x36, x35<- arg1[0] * x8
mov r10, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, r13, rbx; x14, x13<- arg1[3] * x4
xor rdx, rdx
adox r13, r9
adcx r13, r15
setc r12b; spill CF x78 to reg (r12)
clc;
adcx r13, rcx
adox r8, rbx
movzx r12, r12b
lea r10, [ r10 + r8 ]
lea r10, [ r10 + r12 ]
adc r10, 0x0
imul rax, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mov rcx, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r9, r15, rax; x34, x33<- arg1[0] * x7
mov rdx, r13; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x85, x84, size: 2
shrd rdx, r10, 51; x84 <- x83||x81 >> 51
xchg rdx, rbp; x2, swapping with x84, which is currently in rdx
mulx rdx, rbx, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x2
mov r12, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r8, r10, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
add rbx, r10; could be done better, if r0 has been u8 as well
adcx r8, r12
xor rdx, rdx
adox rbx, r15
adcx rbx, rbp
adox r9, r8
adc r9, 0x0
mov rcx, rbx; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x89, x90, size: 2
shrd rcx, r9, 51; x89 <- x88||x86 >> 51
imul r15, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
xchg rdx, rax; x7, swapping with 0x0, which is currently in rdx
mulx rdx, rbp, [ rsi + 0x8 ]; x26, x25<- arg1[1] * x7
mov r12, rdx; preserving value of x26 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r10, r11; x10, x9<- arg1[4] * x1
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r8, r9, r15; x32, x31<- arg1[0] * x6
test al, al
adox r10, rbp
adcx r10, r9
adox r12, r11
mov rdx, -0x3 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, rcx
adcx r8, r12
adox r8, rax
mov rcx, 0x7ffffffffffff ; moving imm to reg
and r14, rcx; x48 <- x43&0x7ffffffffffff
mov rbp, r10; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x94, x95, size: 2
shrd rbp, r8, 51; x94 <- x93||x91 >> 51
imul r11, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov rdx, r11; x3 to rdx
mulx rdx, r11, [ rsi + 0x0 ]; x30, x29<- arg1[0] * x3
mov r9, rdx; preserving value of x30 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx r15, r12, r15; x24, x23<- arg1[1] * x6
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r8, rax, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
test al, al
adox rax, r12
adcx rax, r11
adox r15, r8
adcx r9, r15
add rax, rbp; could be done better, if r0 has been u8 as well
adc r9, 0x0
mov rdx, rax; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x99, x100, size: 2
shrd rdx, r9, 51; x99 <- x98||x96 >> 51
imul rdx, rdx, 0x13; x101 <- x99 * 0x13
lea r14, [ r14 + rdx ]
mov rbp, r14; x104, copying x102 here, cause x102 is needed in a reg for other than x104, namely all: , x103, x104, size: 2
and rbp, rcx; x104 <- x102&0x7ffffffffffff
mov [ rdi + 0x0 ], rbp; out1[0] = x104
shr r14, 51; x103 <- x102>> 51
mov r11, 0x33 ; moving imm to reg
bzhi r13, r13, r11; x85 <- x81 (only least 0x33 bits)
lea r14, [ r14 + r13 ]
mov r12, r14; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x107, x106, size: 2
shr r12, 51; x106 <- x105>> 51
and r14, rcx; x107 <- x105&0x7ffffffffffff
mov [ rdi + 0x8 ], r14; out1[1] = x107
bzhi rbx, rbx, r11; x90 <- x86 (only least 0x33 bits)
lea r12, [ r12 + rbx ]
mov [ rdi + 0x10 ], r12; out1[2] = x108
and r10, rcx; x95 <- x91&0x7ffffffffffff
mov [ rdi + 0x18 ], r10; out1[3] = x95
and rax, rcx; x100 <- x96&0x7ffffffffffff
mov [ rdi + 0x20 ], rax; out1[4] = x100
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; clocked at 2200 MHz
; first cyclecount 44.71, best 34, lastGood 34.612612612612615
; seed 162111320133243 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6184 ms / 500 runs=> 12.368ms/run
; Time spent for assembling and measureing (initial batch_size=225, initial num_batches=101): 3655 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.5910413971539457
; number reverted permutation/ tried permutation: 184 / 249 =73.896%
; number reverted decision/ tried decision: 174 / 252 =69.048%