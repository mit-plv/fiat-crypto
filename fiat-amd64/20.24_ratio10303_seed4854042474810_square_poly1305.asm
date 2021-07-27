SECTION .text
	GLOBAL square_poly1305
square_poly1305:
sub rsp, 0x30 ; last 0x30 (6) for Caller - save regs 
mov [ rsp + 0x0 ], rbx; saving to stack
mov [ rsp + 0x8 ], rbp; saving to stack
mov [ rsp + 0x10 ], r12; saving to stack
mov [ rsp + 0x18 ], r13; saving to stack
mov [ rsp + 0x20 ], r14; saving to stack
mov [ rsp + 0x28 ], r15; saving to stack
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx rax, r10, [ rsi + 0x0 ]; x16, x15<- arg1[0] * arg1[0]
imul r11, [ rsi + 0x10 ], 0x5; x1 <- arg1[2] * 0x5
imul rbx, r11, 0x2; x2 <- x1 * 0x2
imul rbx, rbx, 0x2; x10000 <- x2 * 0x2
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, rbp, rbx; x8, x7<- arg1[1] * x10000
test al, al
adox rbp, r10
adox rax, rbx
imul r12, [ rsi + 0x8 ], 0x2; x4 <- arg1[1] * 0x2
mov r13, 0xfffffffffff ; moving imm to reg
mov r14, rbp; x22, copying x17 here, cause x17 is needed in a reg for other than x22, namely all: , x22, x21, size: 2
and r14, r13; x22 <- x17&0xfffffffffff
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r12, r15, r12; x14, x13<- arg1[0] * x4
mov rdx, r11; x1 to rdx
mulx rdx, r11, [ rsi + 0x10 ]; x6, x5<- arg1[2] * x1
shrd rbp, rax, 44; x21 <- x19||x17 >> 44
add r11, r15; could be done better, if r0 has been u8 as well
adcx r12, rdx
xor rcx, rcx
adox r11, rbp
adox r12, rcx
mov r8, r11; x34, copying x31 here, cause x31 is needed in a reg for other than x34, namely all: , x35, x34, size: 2
shrd r8, r12, 43; x34 <- x33||x31 >> 43
imul r9, [ rsi + 0x10 ], 0x2; x3 <- arg1[2] * 0x2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r9, r10, r9; x12, x11<- arg1[0] * x3
imul rdx, [ rsi + 0x8 ], 0x2; x10001 <- arg1[1] * 0x2
mulx rdx, rbx, [ rsi + 0x8 ]; x10, x9<- arg1[1] * x10001
xor rax, rax
adox rbx, r10
adox r9, rdx
adcx rbx, r8
adc r9, 0x0
mov rcx, rbx; x39, copying x36 here, cause x36 is needed in a reg for other than x39, namely all: , x39, x40, size: 2
shrd rcx, r9, 43; x39 <- x38||x36 >> 43
imul rcx, rcx, 0x5; x41 <- x39 * 0x5
lea r14, [ r14 + rcx ]
mov r15, r14; x44, copying x42 here, cause x42 is needed in a reg for other than x44, namely all: , x43, x44, size: 2
and r15, r13; x44 <- x42&0xfffffffffff
shr r14, 44; x43 <- x42>> 44
mov rbp, 0x7ffffffffff ; moving imm to reg
and r11, rbp; x35 <- x31&0x7ffffffffff
mov [ rdi + 0x0 ], r15; out1[0] = x44
and rbx, rbp; x40 <- x36&0x7ffffffffff
lea r14, [ r14 + r11 ]
mov r12, r14; x47, copying x45 here, cause x45 is needed in a reg for other than x47, namely all: , x46, x47, size: 2
and r12, rbp; x47 <- x45&0x7ffffffffff
shr r14, 43; x46 <- x45>> 43
lea r14, [ r14 + rbx ]
mov [ rdi + 0x10 ], r14; out1[2] = x48
mov [ rdi + 0x8 ], r12; out1[1] = x47
mov rbx, [ rsp + 0x0 ]; restoring from stack
mov rbp, [ rsp + 0x8 ]; restoring from stack
mov r12, [ rsp + 0x10 ]; restoring from stack
mov r13, [ rsp + 0x18 ]; restoring from stack
mov r14, [ rsp + 0x20 ]; restoring from stack
mov r15, [ rsp + 0x28 ]; restoring from stack
add rsp, 0x30 
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; clocked at 2600 MHz
; first cyclecount 26.68, best 19.00836820083682, lastGood 20.24421052631579
; seed 4854042474810 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8934 ms / 500 runs=> 17.868ms/run
; Time spent for assembling and measureing (initial batch_size=464, initial num_batches=101): 6874 ms
; Ratio (time for assembling + measure)/(total runtime for 500runs): 0.769420192522946
; number reverted permutation/ tried permutation: 200 / 236 =84.746%
; number reverted decision/ tried decision: 193 / 265 =72.830%