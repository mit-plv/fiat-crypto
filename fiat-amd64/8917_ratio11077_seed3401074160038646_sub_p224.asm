SECTION .text
	GLOBAL sub_p224
sub_p224:
sub rsp, 0x20
mov rax, [ rsi + 0x0 ];x1, copying arg1[0] here, cause arg1[0] is needed in a reg. It has those deps: "x1--x2, size: 1"
sub rax, [ rdx + 0x0 ]
mov r10, [ rsi + 0x8 ];x3, copying arg1[1] here, cause arg1[1] is needed in a reg. It has those deps: "x3--x4, size: 1"
sbb r10, [ rdx + 0x8 ]
mov r11, [ rsi + 0x10 ];x5, copying arg1[2] here, cause arg1[2] is needed in a reg. It has those deps: "x5--x6, size: 1"
sbb r11, [ rdx + 0x10 ]
mov rcx, [ rsi + 0x18 ];x7, copying arg1[3] here, cause arg1[3] is needed in a reg. It has those deps: "x7--x8, size: 1"
sbb rcx, [ rdx + 0x18 ]
mov r8, 0x0 ; moving imm to reg
mov r9, 0xffffffffffffffff ; moving imm to reg
mov [ rsp + 0x0 ], r15; spilling callerSaver15 to mem
mov r15, r8;x9, copying 0x0 here, cause 0x0 is needed in a reg. It has those deps: "x1--x2, x9, x10--x11, size: 3"
cmovc r15, r9; if CF, x9<- 0xffffffffffffffff (nzVar)
mov r8, 0x1 ; moving imm to reg
mov [ rsp + 0x8 ], r14; spilling callerSaver14 to mem
mov r14, r15;x10000, copying x9 here, cause x9 is needed in a reg. It has those deps: "x10002, x10001, x10000, x14--x15, size: 4"
and r14, r8; x10000 <- x9&0x1
mov r8, 0xffffffff ; moving imm to reg
mov [ rsp + 0x10 ], r13; spilling callerSaver13 to mem
mov r13, r15;x10002, copying x9 here, cause x9 is needed in a reg. It has those deps: "x10002, x10001, x14--x15, size: 3"
and r13, r8; x10002 <- x9&0xffffffff
adox r14, rax
mov [ rdi + 0x0 ], r14; out1[0] = x10
mov rax, 0xffffffff00000000 ; moving imm to reg
seto r14b; spill OF x11 to reg (r14)
mov [ rsp + 0x18 ], r12; spilling callerSaver12 to mem
mov r12, r15;x10001, copying x9 here, cause x9 is needed in a reg. It has those deps: "x10001, x14--x15, size: 2"
and r12, rax; x10001 <- x9&0xffffffff00000000
add r14b, 0x7F; load flag from rm/8 into OF, clears other flag. NOTE, if operand1 is not a byte reg, this fails.
seto r14b; since that has deps, restore it where ever it was
adox r10, r12
adox r15, r11
adox rcx, r13
mov [ rdi + 0x10 ], r15; out1[2] = x14
mov [ rdi + 0x18 ], rcx; out1[3] = x16
mov [ rdi + 0x8 ], r10; out1[1] = x12
mov r15, [ rsp + 0x0 ] ; pop
mov r14, [ rsp + 0x8 ] ; pop
mov r13, [ rsp + 0x10 ] ; pop
mov r12, [ rsp + 0x18 ] ; pop
add rsp, 0x20 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.1077
; seed 3401074160038646 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 18641 ms / 9500 evals=> 1.9622105263157894ms/eval
; Time spent for assembling and measureing (initial batch_size=485, initial num_batches=31): 6977 ms
; number of used evaluations: 9500
; Ratio (time for assembling + measure)/(total runtime for 9500 evals): 0.3742824955742718
; number reverted permutation/ tried permutation: 4377 / 4794 =91.302%
; number reverted decision/ tried decision: 4323 / 4705 =91.881%