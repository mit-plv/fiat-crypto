SECTION .text
	GLOBAL mul_curve25519
mul_curve25519:
sub rsp, 0x88
imul rax, [ rdx + 0x20 ], 0x13; x10000 <- arg2[4] * 0x13
imul r10, [ rdx + 0x18 ], 0x13; x10001 <- arg2[3] * 0x13
imul r11, [ rdx + 0x10 ], 0x13; x10002 <- arg2[2] * 0x13
imul rcx, [ rdx + 0x8 ], 0x13; x10003 <- arg2[1] * 0x13
mov r8, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
mulx r9, r15, rax; x20, x19<- arg1[1] * x10000
mov rdx, [ r8 + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mulx r14, r13, [ rsi + 0x0 ]; x50, x49<- arg1[0] * arg2[0]
mov rdx, r10; x10001 to rdx
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mulx r10, r12, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x10001
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mov rbp, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x28 ], rbx; spilling callerSaverbx to mem
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
mulx rbx, rdi, r11; x14, x13<- arg1[3] * x10002
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x38 ], r14; spilling x50 to mem
mulx rcx, r14, rcx; x8, x7<- arg1[4] * x10003
mov [ rsp + 0x40 ], r9; spilling x20 to mem
xor r9, r9
adox r14, rdi
adcx r14, r12
seto r12b; spill OF x52 to reg (r12)
mov rdi, -0x3 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r14, r15
setc r15b; spill CF x56 to reg (r15)
clc;
adcx r14, r13
movzx r12, r12b
lea rbx, [ rbx + rcx ]
lea rbx, [ rbx + r12 ]
movzx r15, r15b
lea r10, [ r10 + rbx ]
lea r10, [ r10 + r15 ]
adox r10, [ rsp + 0x40 ]
adcx r10, [ rsp + 0x38 ]
mov r13, r14; x67, copying x63 here, cause x63 is needed in a reg for other than x67, namely all: , x67, x68, size: 2
shrd r13, r10, 51; x67 <- x65||x63 >> 51
mov rcx, 0x33 ; moving imm to reg
bzhi r14, r14, rcx; x68 <- x63 (only least 0x33 bits)
mov rdx, [ r8 + 0x8 ]; arg2[1] to rdx
mulx r12, r15, [ rsi + 0x0 ]; x48, x47<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r10, [ r8 + 0x0 ]; x40, x39<- arg1[1] * arg2[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, rcx, rax; x16, x15<- arg1[2] * x10000
mov rdx, rbp; x10001 to rdx
mov [ rsp + 0x48 ], r14; spilling x68 to mem
mulx rdi, r14, [ rsi + 0x18 ]; x12, x11<- arg1[3] * x10001
xchg rdx, r11; x10002, swapping with x10001, which is currently in rdx
mov [ rsp + 0x50 ], r12; spilling x48 to mem
mulx rdx, r12, [ rsi + 0x20 ]; x6, x5<- arg1[4] * x10002
adox r12, r14
clc;
adcx r12, rcx
seto cl; spill OF x118 to reg (rcx)
mov r14, -0x2 ; moving imm to reg
inc r14; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r10
setc r10b; spill CF x122 to reg (r10)
clc;
adcx r12, r15
seto r15b; spill OF x126 to reg (r15)
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, r13
movzx rcx, cl
lea rdi, [ rdi + rdx ]
lea rdi, [ rdi + rcx ]
movzx r10, r10b
lea r9, [ r9 + rdi ]
lea r9, [ r9 + r10 ]
movzx r15, r15b
lea rbx, [ rbx + r9 ]
lea rbx, [ rbx + r15 ]
adcx rbx, [ rsp + 0x50 ]
adox rbx, r14
mov r13, r12; x136, copying x133 here, cause x133 is needed in a reg for other than x136, namely all: , x136, x137, size: 2
shrd r13, rbx, 51; x136 <- x135||x133 >> 51
mov rdx, 0x7ffffffffffff ; moving imm to reg
and r12, rdx; x137 <- x133&0x7ffffffffffff
mov rcx, rdx; preserving value of 0x7ffffffffffff into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r15, [ r8 + 0x10 ]; x46, x45<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rdi, r9, [ r8 + 0x8 ]; x38, x37<- arg1[1] * arg2[1]
mov rdx, [ r8 + 0x0 ]; arg2[0] to rdx
mulx rbx, r14, [ rsi + 0x10 ]; x32, x31<- arg1[2] * arg2[0]
mov rdx, rax; x10000 to rdx
mulx rax, rcx, [ rsi + 0x18 ]; x10, x9<- arg1[3] * x10000
mov [ rsp + 0x58 ], r12; spilling x137 to mem
mov r12, rdx; preserving value of x10000 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x60 ], r10; spilling x46 to mem
mulx r11, r10, r11; x4, x3<- arg1[4] * x10001
adox r10, rcx
adcx r10, r14
setc r14b; spill CF x106 to reg (r14)
clc;
adcx r10, r9
seto r9b; spill OF x102 to reg (r9)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r15
setc r15b; spill CF x110 to reg (r15)
clc;
adcx r10, r13
movzx r9, r9b
lea rax, [ rax + r11 ]
lea rax, [ rax + r9 ]
movzx r14, r14b
lea rbx, [ rbx + rax ]
lea rbx, [ rbx + r14 ]
movzx r15, r15b
lea rdi, [ rdi + rbx ]
lea rdi, [ rdi + r15 ]
adox rdi, [ rsp + 0x60 ]
adc rdi, 0x0
mov r13, r10; x141, copying x138 here, cause x138 is needed in a reg for other than x141, namely all: , x141, x142, size: 2
shrd r13, rdi, 51; x141 <- x140||x138 >> 51
mov r11, 0x33 ; moving imm to reg
bzhi r10, r10, r11; x142 <- x138 (only least 0x33 bits)
mov rdx, [ r8 + 0x18 ]; arg2[3] to rdx
mulx r9, r14, [ rsi + 0x0 ]; x44, x43<- arg1[0] * arg2[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r15, rax, [ r8 + 0x10 ]; x36, x35<- arg1[1] * arg2[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rbx, rdi, [ r8 + 0x8 ]; x30, x29<- arg1[2] * arg2[1]
mov rdx, [ r8 + 0x0 ]; arg2[0] to rdx
mulx r11, rcx, [ rsi + 0x18 ]; x26, x25<- arg1[3] * arg2[0]
mov rdx, r12; x10000 to rdx
mov [ rsp + 0x68 ], r10; spilling x142 to mem
mulx rdx, r10, [ rsi + 0x20 ]; x2, x1<- arg1[4] * x10000
adox r10, rcx
clc;
adcx r10, rdi
seto dil; spill OF x86 to reg (rdi)
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, rax
seto al; spill OF x94 to reg (rax)
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r10, r14
seto r14b; spill OF x98 to reg (r14)
mov [ rsp + 0x70 ], r9; spilling x44 to mem
mov r9, -0x3 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r10, r13
movzx rdi, dil
lea r11, [ r11 + rdx ]
lea r11, [ r11 + rdi ]
adcx rbx, r11
movzx rax, al
lea r15, [ r15 + rbx ]
lea r15, [ r15 + rax ]
movzx r14, r14b
lea r15, [ r14 + r15 ]
mov r14, [ rsp + 0x70 ]
lea r15, [r14+r15]
adox r15, rcx
mov r13, r10; x146, copying x143 here, cause x143 is needed in a reg for other than x146, namely all: , x146, x147, size: 2
shrd r13, r15, 51; x146 <- x145||x143 >> 51
mov rdx, 0x33 ; moving imm to reg
bzhi r10, r10, rdx; x147 <- x143 (only least 0x33 bits)
mov rdx, [ r8 + 0x20 ]; arg2[4] to rdx
mulx rdx, rdi, [ rsi + 0x0 ]; x42, x41<- arg1[0] * arg2[4]
mov rax, rdx; preserving value of x42 into a new reg
mov rdx, [ r8 + 0x18 ]; saving arg2[3] in rdx.
mulx r14, r11, [ rsi + 0x8 ]; x34, x33<- arg1[1] * arg2[3]
mov rdx, [ r8 + 0x8 ]; arg2[1] to rdx
mulx rbx, r15, [ rsi + 0x18 ]; x24, x23<- arg1[3] * arg2[1]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rcx, r9, [ r8 + 0x10 ]; x28, x27<- arg1[2] * arg2[2]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x78 ], r10; spilling x147 to mem
mov [ rsp + 0x80 ], rax; spilling x42 to mem
mulx r10, rax, [ r8 + 0x0 ]; x22, x21<- arg1[4] * arg2[0]
adox rax, r15
clc;
adcx rax, r9
setc r15b; spill CF x74 to reg (r15)
clc;
adcx rax, r11
setc r11b; spill CF x78 to reg (r11)
clc;
adcx rax, rdi
seto dil; spill OF x70 to reg (rdi)
mov r9, -0x2 ; moving imm to reg
inc r9; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rax, r13
movzx rdi, dil
lea rbx, [ rbx + r10 ]
lea rbx, [ rbx + rdi ]
movzx r15, r15b
lea rcx, [ rcx + rbx ]
lea rcx, [ rcx + r15 ]
movzx r11, r11b
lea r14, [ r14 + rcx ]
lea r14, [ r14 + r11 ]
adcx r14, [ rsp + 0x80 ]
mov r13, 0x0 ; moving imm to reg
adox r14, r13
mov r10, rax; x151, copying x148 here, cause x148 is needed in a reg for other than x151, namely all: , x151, x152, size: 2
shrd r10, r14, 51; x151 <- x150||x148 >> 51
imul r10, r10, 0x13; x153 <- x151 * 0x13
mov rdi, 0x33 ; moving imm to reg
bzhi rax, rax, rdi; x152 <- x148 (only least 0x33 bits)
add r10, [ rsp + 0x48 ]
mov r15, r10; x155, copying x154 here, cause x154 is needed in a reg for other than x155, namely all: , x155, x156, size: 2
shr r15, 51; x155 <- x154>> 51
mov r11, 0x7ffffffffffff ; moving imm to reg
and r10, r11; x156 <- x154&0x7ffffffffffff
add r15, [ rsp + 0x58 ]
mov rbx, r15; x158, copying x157 here, cause x157 is needed in a reg for other than x158, namely all: , x158, x159, size: 2
shr rbx, 51; x158 <- x157>> 51
and r15, r11; x159 <- x157&0x7ffffffffffff
add rbx, [ rsp + 0x68 ]
mov rcx, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ rcx + 0x0 ], r10; out1[0] = x156
mov [ rcx + 0x8 ], r15; out1[1] = x159
mov [ rcx + 0x10 ], rbx; out1[2] = x160
mov r14, [ rsp + 0x78 ]; TMP = x147
mov [ rcx + 0x18 ], r14; out1[3] = TMP
mov [ rcx + 0x20 ], rax; out1[4] = x152
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
mov rbx, [ rsp + 0x28 ] ; pop
add rsp, 0x88 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.9377
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 573 ms / 10 evals=> 57.3ms/eval
; Time spent for assembling and measureing (initial batch_size=111, initial num_batches=31): 41 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.07155322862129145
; number reverted permutation/ tried permutation: 1 / 4 =25.000%
; number reverted decision/ tried decision: 3 / 6 =50.000%