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
imul rax, [ rdx + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
imul r10, [ rdx + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
mov r11, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rbx, rbp, r10; x14, x13<- arg1[3] * x10002
mov rdx, rax; x10003 to rdx
mulx rdx, rax, [ rsi + 0x20 ]; x8, x7<- arg1[4] * x10003
imul r12, [ r11 + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
imul r13, [ r11 + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
xor r14, r14
adox rax, rbp
adox rbx, rdx
mov rdx, r12; x10001 to rdx
mulx r12, r15, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x10001
mov rcx, rdx; preserving value of x10001 into a new reg
mov rdx, [ r11 + 0x0 ]; saving arg2[0] in rdx.
mulx r8, r9, [ rsi + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbp, r14, r13; x20, x19<- arg1[1] * x10000
adcx rax, r15
mov rdx, rcx; x10001 to rdx
mulx rcx, r15, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x10001
mov [ rsp + 0x0 ], rdi; spilling out1 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r14
mov r14, rdx; preserving value of x10001 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mov [ rsp + 0x8 ], rcx; spilling x12 to mem
mulx rdi, rcx, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x10 ], rdi; spilling x48 to mem
mulx r10, rdi, r10; x6, x5<- arg1[4] * x10002
adcx r12, rbx
adox rbp, r12
test al, al
adox rax, r9
adox r8, rbp
mov rbx, rax; x67, copying x63 here, cause x63 is needed in a reg for other than x67, namely all: , x68, x67, size: 2
shrd rbx, r8, 51; x67 <- x65||x63 >> 51
test al, al
adox rdi, r15
mov rdx, r13; x10000 to rdx
mulx r13, r9, [ rsi + 0x10 ]; x16, x15<- arg1[2] * x10000
mov r15, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, rbp, [ r11 + 0x0 ]; x32, x31<- arg1[2] * arg2[0]
adcx rdi, r9
adox r10, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, r9, [ r11 + 0x0 ]; x40, x39<- arg1[1] * arg2[0]
adcx r13, r10
test al, al
adox rdi, r9
adox r8, r13
adcx rdi, rcx
adcx r8, [ rsp + 0x10 ]
xor rcx, rcx
adox rdi, rbx
adox r8, rcx
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx rbx, r10, r15; x10, x9<- arg1[3] * x10000
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mulx r9, r13, [ rsi + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
mov rcx, rdi; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x136, x137, size: 2
shrd rcx, r8, 51; x136 <- x135||x133 >> 51
mov rdx, r14; x10001 to rdx
mulx rdx, r14, [ rsi + 0x20 ]; x4, x3<- arg1[4] * x10001
test al, al
adox r14, r10
mov r8, rdx; preserving value of x4 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r15, r10, r15; x2, x1<- arg1[4] * x10000
adox rbx, r8
adcx r14, rbp
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rbp, r8, [ r11 + 0x10 ]; x46, x45<- arg1[0] * arg2[2]
adcx r12, rbx
add r14, r13; could be done better, if r0 has been u8 as well
adcx r9, r12
mov rdx, [ r11 + 0x18 ]; arg2[3] to rdx
mulx r13, rbx, [ rsi + 0x0 ]; x44, x43<- arg1[0] * arg2[3]
test al, al
adox r14, r8
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx r8, r12, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
mov rdx, [ r11 + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x18 ], r13; spilling x44 to mem
mov [ rsp + 0x20 ], rbx; spilling x43 to mem
mulx r13, rbx, [ rsi + 0x10 ]; x30, x29<- arg1[2] * arg2[1]
adcx r14, rcx
adox rbp, r9
adc rbp, 0x0
mov rcx, r14; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x142, x141, size: 2
shrd rcx, rbp, 51; x141 <- x140||x138 >> 51
add r10, r12; could be done better, if r0 has been u8 as well
adcx r8, r15
xor r15, r15
adox r10, rbx
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mulx r9, r12, [ rsi + 0x8 ]; x36, x35<- arg1[1] * arg2[2]
adox r13, r8
mov rdx, [ r11 + 0x0 ]; arg2[0] to rdx
mulx rbx, rbp, [ rsi + 0x20 ]; x22, x21<- arg1[4] * arg2[0]
adcx r10, r12
mov r8, -0x3 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, [ rsp + 0x20 ]
adcx r9, r13
adox r9, [ rsp + 0x18 ]
mov rdx, [ r11 + 0x20 ]; arg2[4] to rdx
mulx rdx, r12, [ rsi + 0x0 ]; x42, x41<- arg1[0] * arg2[4]
add r10, rcx; could be done better, if r0 has been u8 as well
mov rcx, rdx; preserving value of x42 into a new reg
mov rdx, [ r11 + 0x8 ]; saving arg2[1] in rdx.
mulx r13, r15, [ rsi + 0x18 ]; x24, x23<- arg1[3] * arg2[1]
mov rdx, [ r11 + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x28 ], rax; spilling x63 to mem
mulx r8, rax, [ rsi + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
adc r9, 0x0
mov [ rsp + 0x30 ], rcx; spilling x42 to mem
mov rcx, r10; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x146, x147, size: 2
shrd rcx, r9, 51; x146 <- x145||x143 >> 51
test al, al
adox rbp, r15
adcx rbp, rax
adox r13, rbx
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r15, [ r11 + 0x18 ]; x34, x33<- arg1[1] * arg2[3]
adcx r8, r13
test al, al
adox rbp, r15
adcx rbp, r12
adox rbx, r8
mov r12, -0x2 ; moving imm to reg
inc r12; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rcx
adcx rbx, [ rsp + 0x30 ]
mov rax, 0x7ffffffffffff ; moving imm to reg
seto r9b; spill OF x149 to reg (r9)
and r10, rax; x147 <- x143&0x7ffffffffffff
movzx rcx, r9b; x150, copying x149 here, cause x149 is needed in a reg for other than x150, namely all: , x150, size: 1
lea rcx, [ rcx + rbx ]
mov r13, rbp; x151, copying x148 here, cause x148 is needed in a reg for other than x151, namely all: , x152, x151, size: 2
shrd r13, rcx, 51; x151 <- x150||x148 >> 51
and rbp, rax; x152 <- x148&0x7ffffffffffff
mov r15, [ rsp + 0x28 ]; x68, copying x63 here, cause x63 is needed in a reg for other than x68, namely all: , x68, size: 1
and r15, rax; x68 <- x63&0x7ffffffffffff
and r14, rax; x142 <- x138&0x7ffffffffffff
imul r13, r13, 0x13; x153 <- x151 * 0x13
lea r15, [ r15 + r13 ]
and rdi, rax; x137 <- x133&0x7ffffffffffff
mov r8, r15; x156, copying x154 here, cause x154 is needed in a reg for other than x156, namely all: , x156, x155, size: 2
and r8, rax; x156 <- x154&0x7ffffffffffff
shr r15, 51; x155 <- x154>> 51
lea r15, [ r15 + rdi ]
mov r9, r15; x159, copying x157 here, cause x157 is needed in a reg for other than x159, namely all: , x159, x158, size: 2
and r9, rax; x159 <- x157&0x7ffffffffffff
shr r15, 51; x158 <- x157>> 51
lea r15, [ r15 + r14 ]
mov rbx, [ rsp + 0x0 ]; load m64 out1 to register64
mov [ rbx + 0x10 ], r15; out1[2] = x160
mov [ rbx + 0x20 ], rbp; out1[4] = x152
mov [ rbx + 0x8 ], r9; out1[1] = x159
mov [ rbx + 0x0 ], r8; out1[0] = x156
mov [ rbx + 0x18 ], r10; out1[3] = x147
mov rbx, [ rsp + 0x38 ]; restoring from stack
mov rbp, [ rsp + 0x40 ]; restoring from stack
mov r12, [ rsp + 0x48 ]; restoring from stack
mov r13, [ rsp + 0x50 ]; restoring from stack
mov r14, [ rsp + 0x58 ]; restoring from stack
mov r15, [ rsp + 0x60 ]; restoring from stack
add rsp, 0x68 
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; clocked at 2200 MHz
; first cyclecount 59.185, best 42.32673267326733, lastGood 43.482587064676615
; seed 2293761300508191 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 569792 ms / 60000 runs=> 9.496533333333334ms/run
; Time spent for assembling and measureing (initial batch_size=202, initial num_batches=101): 250954 ms
; Ratio (time for assembling + measure)/(total runtime for 60000runs): 0.44043089408064695
; number reverted permutation/ tried permutation: 23829 / 29920 =79.642%
; number reverted decision/ tried decision: 19633 / 30081 =65.267%