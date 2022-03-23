SECTION .text
	GLOBAL square_poly1305
square_poly1305:
sub rsp, 0x30
mov rax, 0x1 ; moving imm to reg
shlx r10, [ rsi + 0x8 ], rax; x4 <- arg1[1] * 0x2 (shlx does not change the flags)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rcx, r11, rdx; x10_1, x10_0<- arg1[0]^2
imul rdx, [ rsi + 0x10 ], 0x14; x10000 <- arg1[2] * 0x14
mov r8, [ rsi + 0x10 ]; load m64 arg1[2] to register64
lea r9, [r8 + 4 * r8]; x1 <- arg1[2] * 5 (by add to itself*4)
mulx rax, r8, [ rsi + 0x8 ]; x6_1, x6_0<- arg1[1] * x10000 (_0*_0)
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x0 ], rbx; spilling calSv-rbx to mem
mov [ rsp + 0x8 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, r9; x5_1, x5_0<- arg1[2] * x1 (_0*_0)
mov rdx, [ rsi + 0x10 ]; load m64 arg1[2] to register64
mov r9, rdx; load m64 x3 to register64
shl r9, 0x1; x3 <- arg1[2] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x10 ], r12; spilling calSv-r12 to mem
mov [ rsp + 0x18 ], r13; spilling calSv-r13 to mem
mulx r13, r12, r9; x8_1, x8_0<- arg1[0] * x3 (_0*_0)
mov rdx, [ rsi + 0x8 ]; load m64 arg1[1] to register64
mov r9, rdx; load m64 x10001 to register64
shl r9, 0x1; x10001 <- arg1[1] * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x20 ], r14; spilling calSv-r14 to mem
mov [ rsp + 0x28 ], r15; spilling calSv-r15 to mem
mulx r15, r14, r9; x7_1, x7_0<- arg1[1] * x10001 (_0*_0)
mov rdx, r10; x4 to rdx
mulx r9, r10, [ rsi + 0x0 ]; x9_1, x9_0<- arg1[0] * x4 (_0*_0)
add rbx, r10; could be done better, if r0 has been u8 as well
adcx r9, rbp
add r8, r11; could be done better, if r0 has been u8 as well
adcx rcx, rax
mov rdx, r8;x12, copying x11_0 here, cause x11_0 is needed in a reg. It has those deps: "x12, x13, size: 2", current hard deps: ""
shrd rdx, rcx, 44; x12 <- x11_1||x11_0 >> 44
add r14, r12; could be done better, if r0 has been u8 as well
adcx r13, r15
mov r11, 0xfffffffffff ; moving imm to reg
and r8, r11; x13 <- x11_0&0xfffffffffff
adox rbx, rdx
mov rax, 0x0 ; moving imm to reg
adox r9, rax
mov rbp, 0x2b ; moving imm to reg
bzhi r12, rbx, rbp; x18 <- x16_0 (only least 0x2b bits)
shrd rbx, r9, 43; x17 <- x16_1||x16_0 >> 43
add r14, rbx; could be done better, if r0 has been u8 as well
adc r13, 0x0; add CF to r0's alloc
mov r15, r14;x20, copying x19_0 here, cause x19_0 is needed in a reg. It has those deps: "x20, x21, size: 2", current hard deps: ""
shrd r15, r13, 43; x20 <- x19_1||x19_0 >> 43

; imul works
; imul r10, r15, 5
lea r10, [r15 + 4 * r15]; x22 <- x20 * 5 (by add to itself*4)

lea r8, [ r8 + r10 ]
bzhi rcx, r14, rbp; x21 <- x19_0 (only least 0x2b bits)
mov rdx, r8;x24, copying x23 here, cause x23 is needed in a reg. It has those deps: "x24, x25, size: 2", current hard deps: ""
shr rdx, 44; x24 <- x23>> 44
lea rdx, [ rdx + r12 ]
mov r9, rdx;x27, copying x26 here, cause x26 is needed in a reg. It has those deps: "x27, x28, size: 2", current hard deps: ""
shr r9, 43; x27 <- x26>> 43
bzhi r12, rdx, rbp; x28 <- x26 (only least 0x2b bits)
lea r9, [ r9 + rcx ]
and r8, r11; x25 <- x23&0xfffffffffff
mov [ rdi + 0x10 ], r9; out1[2] = x29
mov [ rdi + 0x8 ], r12; out1[1] = x28
mov [ rdi + 0x0 ], r8; out1[0] = x25
mov rbx, [ rsp + 0x0 ] ; pop
mov rbp, [ rsp + 0x8 ] ; pop
mov r12, [ rsp + 0x10 ] ; pop
mov r13, [ rsp + 0x18 ] ; pop
mov r14, [ rsp + 0x20 ] ; pop
mov r15, [ rsp + 0x28 ] ; pop
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.1549
; seed 1785685356 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; time needed: 441 ms / 50 evals=> 8.82ms/eval
; Time spent for assembling and measureing (initial batch_size=166, initial num_batches=31): 45 ms
; number of used evaluations: 50
; Ratio (time for assembling + measure)/(total runtime for 50 evals): 0.10204081632653061
; number reverted permutation/ tried permutation: 7 / 26 =26.923%
; number reverted decision/ tried decision: 5 / 23 =21.739%
