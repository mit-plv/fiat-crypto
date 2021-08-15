SECTION .text
	GLOBAL square_curve25519
square_curve25519:
sub rsp, 0x28
imul rax, [ rsi + 0x20 ], 0x13; x1 <- arg1[4] * 0x13
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r10, r11, [ rsi + 0x0 ]; x38, x37<- arg1[0] * arg1[0]
imul rdx, rax, 0x2; x2 <- x1 * 0x2
imul rcx, [ rsi + 0x18 ], 0x13; x4 <- arg1[3] * 0x13
mulx r8, r9, [ rsi + 0x8 ]; x22, x21<- arg1[1] * x2
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
imul r15, rcx, 0x2; x5 <- x4 * 0x2
xchg rdx, r15; x5, swapping with x2, which is currently in rdx
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mulx rdx, r14, [ rsi + 0x10 ]; x18, x17<- arg1[2] * x5
test al, al
adox r14, r9
adox r8, rdx
adcx r14, r11
adcx r10, r8
mov r11, r14; x47, copying x43 here, cause x43 is needed in a reg for other than x47, namely all: , x47, x48, size: 2
shrd r11, r10, 51; x47 <- x45||x43 >> 51
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r8, r15; x16, x15<- arg1[2] * x2
imul rdx, [ rsi + 0x8 ], 0x2; x8 <- arg1[1] * 0x2
mulx rdx, r10, [ rsi + 0x0 ]; x36, x35<- arg1[0] * x8
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mov r13, rdx; preserving value of x36 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mulx rcx, r12, rcx; x14, x13<- arg1[3] * x4
add r12, r8; could be done better, if r0 has been u8 as well
adcx r9, rcx
test al, al
adox r12, r10
adox r13, r9
adcx r12, r11
adc r13, 0x0
imul rdx, [ rsi + 0x10 ], 0x2; x7 <- arg1[2] * 0x2
mulx r11, r8, [ rsi + 0x0 ]; x34, x33<- arg1[0] * x7
mov r10, r12; x84, copying x81 here, cause x81 is needed in a reg for other than x84, namely all: , x84, x85, size: 2
shrd r10, r13, 51; x84 <- x83||x81 >> 51
mov rcx, rdx; preserving value of x7 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r15, r9, r15; x12, x11<- arg1[3] * x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x20 ], rbp; spilling callerSaverbp to mem
mulx r13, rbp, [ rsi + 0x8 ]; x28, x27<- arg1[1] * arg1[1]
xor rdx, rdx
adox r9, rbp
adcx r9, r8
seto r8b; spill OF x66 to reg (r8)
mov rbp, -0x3 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug 7; load -3, increase it, save it as -2). #last resort
adox r9, r10
movzx r8, r8b
lea r13, [ r13 + r15 ]
lea r13, [ r13 + r8 ]
adcx r11, r13
adox r11, rdx
mov r10, r9; x89, copying x86 here, cause x86 is needed in a reg for other than x89, namely all: , x90, x89, size: 2
shrd r10, r11, 51; x89 <- x88||x86 >> 51
imul r15, [ rsi + 0x18 ], 0x2; x6 <- arg1[3] * 0x2
xchg rdx, rcx; x7, swapping with 0x0, which is currently in rdx
mulx rdx, r8, [ rsi + 0x8 ]; x26, x25<- arg1[1] * x7
xchg rdx, r15; x6, swapping with x26, which is currently in rdx
mulx r13, r11, [ rsi + 0x0 ]; x32, x31<- arg1[0] * x6
mov rcx, rdx; preserving value of x6 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rax, rbp, rax; x10, x9<- arg1[4] * x1
add rbp, r8; could be done better, if r0 has been u8 as well
adcx r15, rax
xor rdx, rdx
adox rbp, r11
adox r13, r15
adcx rbp, r10
adc r13, 0x0
imul r10, [ rsi + 0x20 ], 0x2; x3 <- arg1[4] * 0x2
mov r8, rdx; preserving value of 0x0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r10, r11, r10; x30, x29<- arg1[0] * x3
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx rax, r15, [ rsi + 0x10 ]; x20, x19<- arg1[2] * arg1[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r8, rcx; x24, x23<- arg1[1] * x6
add r15, r8; could be done better, if r0 has been u8 as well
setc dl; spill CF x50 to reg (rdx)
mov r8, rbp; x94, copying x91 here, cause x91 is needed in a reg for other than x94, namely all: , x95, x94, size: 2
shrd r8, r13, 51; x94 <- x93||x91 >> 51
xor r13, r13
adox r15, r11
adcx r15, r8
movzx rdx, dl
lea rcx, [ rcx + rax ]
lea rcx, [ rcx + rdx ]
adox r10, rcx
adc r10, 0x0
mov r11, r15; x99, copying x96 here, cause x96 is needed in a reg for other than x99, namely all: , x99, x100, size: 2
shrd r11, r10, 51; x99 <- x98||x96 >> 51
mov rax, 0x7ffffffffffff ; moving imm to reg
and r14, rax; x48 <- x43&0x7ffffffffffff
and r9, rax; x90 <- x86&0x7ffffffffffff
imul r11, r11, 0x13; x101 <- x99 * 0x13
lea r14, [ r14 + r11 ]
and r12, rax; x85 <- x81&0x7ffffffffffff
mov rdx, r14; x103, copying x102 here, cause x102 is needed in a reg for other than x103, namely all: , x104, x103, size: 2
shr rdx, 51; x103 <- x102>> 51
and r14, rax; x104 <- x102&0x7ffffffffffff
mov r8, 0x33 ; moving imm to reg
bzhi r15, r15, r8; x100 <- x96 (only least 0x33 bits)
lea rdx, [ rdx + r12 ]
mov [ rdi + 0x0 ], r14; out1[0] = x104
mov [ rdi + 0x20 ], r15; out1[4] = x100
bzhi rbp, rbp, r8; x95 <- x91 (only least 0x33 bits)
mov [ rdi + 0x18 ], rbp; out1[3] = x95
mov rcx, rdx; x106, copying x105 here, cause x105 is needed in a reg for other than x106, namely all: , x106, x107, size: 2
shr rcx, 51; x106 <- x105>> 51
lea rcx, [ rcx + r9 ]
and rdx, rax; x107 <- x105&0x7ffffffffffff
mov [ rdi + 0x8 ], rdx; out1[1] = x107
mov [ rdi + 0x10 ], rcx; out1[2] = x108
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
mov rbp, [ rsp + 0x20 ] ; pop
add rsp, 0x28 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.1770
; seed 389709233 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; time needed: 4266 ms / 500 evals=> 8.532ms/eval
; Time spent for assembling and measureing (initial batch_size=148, initial num_batches=31): 566 ms
; number of used evaluations: 500
; Ratio (time for assembling + measure)/(total runtime for 500 evals): 0.1326769807782466
; number reverted permutation/ tried permutation: 195 / 235 =82.979%
; number reverted decision/ tried decision: 189 / 265 =71.321%
