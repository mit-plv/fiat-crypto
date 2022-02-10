SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x168
mov rax, 0x1 ; moving imm to reg
shlx r10, [ rsi + 0x40 ], rax; x10000 <- arg1[8] * 2 (by shlx 1, which does not change the flags)
mov r11, [ rsi + 0x28 ]; load m64 arg1[5] to register64
mov rdx, r11; load m64 x11 to register64

; x11 <- arg1[5] * 2 * 2(by shl 2)
; x10007 <- x11 * 2 (by shl 1)
shl rdx, 0x2 ; x10007 <- x11 * 2 * 2 (by shl 2)

mov r11, [ rsi + 0x38 ]; load m64 arg1[7] to register64
lea rcx, [r11 + r11]; x10002 <- arg1[7] * 2 (by add to itself)
mov r11, [ rsi + 0x30 ]; load m64 arg1[6] to register64
lea r8, [r11 + r11]; x10004 <- arg1[6] * 2 (by add to itself)
mov r11, [ rsi + 0x28 ]; load m64 arg1[5] to register64
mov r9, r11; load m64 x10006 to register64
shl r9, 0x1; x10006 <- arg1[5] * 2 (by shl 1)
mov r11, [ rsi + 0x40 ]; load m64 arg1[8] to register64
mov rax, r11; load m64 x2 to register64
shl rax, 0x1; x2 <- arg1[8] * 2 (by shl 1)
shl rax, 0x1; x10001 <- x2 * 2 (by shl 1)
mov r11, [ rsi + 0x40 ]; load m64 arg1[8] to register64
mov [ rsp + 0x0 ], rbx; spilling calSv-rbx to mem
mov rbx, r11; load m64 x3 to register64
shl rbx, 0x1; x3 <- arg1[8] * 2 (by shl 1)
mov r11, [ rsi + 0x38 ]; load m64 arg1[7] to register64
mov [ rsp + 0x8 ], rbp; spilling calSv-rbp to mem
mov rbp, r11; load m64 x5 to register64
shl rbp, 0x1; x5 <- arg1[7] * 2 (by shl 1)
imul r11, rbp, 0x2; x10003 <- x5 * 0x2
imul rbp, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov [ rsp + 0x10 ], r12; spilling calSv-r12 to mem
imul r12, [ rsi + 0x30 ], 0x2; x8 <- arg1[6] * 0x2
mov [ rsp + 0x18 ], r13; spilling calSv-r13 to mem
lea r13, [r12 + r12]; x10005 <- x8 * 2 (by add to itself)
mov r12, [ rsi + 0x30 ]; load m64 arg1[6] to register64
mov [ rsp + 0x20 ], r14; spilling calSv-r14 to mem
mov r14, r12; load m64 x9 to register64
shl r14, 0x1; x9 <- arg1[6] * 2 (by shl 1)
mov r12, [ rsi + 0x28 ]; load m64 arg1[5] to register64
mov [ rsp + 0x28 ], r15; spilling calSv-r15 to mem
lea r15, [r12 + r12]; x12 <- arg1[5] * 2 (by add to itself)
mov r12, [ rsi + 0x20 ]; load m64 arg1[4] to register64
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
lea rdi, [r12 + r12]; x13 <- arg1[4] * 2 (by add to itself)
mov r12, 0x1 ; moving imm to reg
mov [ rsp + 0x38 ], rbp; spilling x6 to mem
shlx rbp, [ rsi + 0x18 ], r12; x14 <- arg1[3] * 2 (by shlx 1, which does not change the flags)
mov [ rsp + 0x40 ], rbp; spilling x14 to mem
shlx rbp, [ rsi + 0x10 ], r12; x15 <- arg1[2] * 2 (by shlx 1, which does not change the flags)
mov r12, [ rsi + 0x8 ]; load m64 arg1[1] to register64
mov [ rsp + 0x48 ], rbp; spilling x15 to mem
mov rbp, r12; load m64 x16 to register64
shl rbp, 0x1; x16 <- arg1[1] * 2 (by shl 1)
mov r12, rdx; preserving value of x10007 into a new reg
mov rdx, [ rsi + 0x40 ]; saving arg1[8] in rdx.
mov [ rsp + 0x50 ], r14; spilling x9 to mem
mov [ rsp + 0x58 ], r15; spilling x12 to mem
mulx r15, r14, r10; x17_1, x17_0<- arg1[8] * x10000 (_0*_0)
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x60 ], r15; spilling x17_1 to mem
mulx r15, r10, rcx; x19_1, x19_0<- arg1[7] * x10002 (_0*_0)
mov rdx, r8; x10004 to rdx
mulx rcx, r8, [ rsi + 0x30 ]; x22_1, x22_0<- arg1[6] * x10004 (_0*_0)
mov rdx, r9; x10006 to rdx
mov [ rsp + 0x68 ], r14; spilling x17_0 to mem
mulx r14, r9, [ rsi + 0x28 ]; x26_1, x26_0<- arg1[5] * x10006 (_0*_0)
mov rdx, r12; x10007 to rdx
mov [ rsp + 0x70 ], rdi; spilling x13 to mem
mulx rdi, r12, [ rsi + 0x20 ]; x30_1, x30_0<- arg1[4] * x10007 (_0*_0)
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x78 ], rdi; spilling x30_1 to mem
mov [ rsp + 0x80 ], r12; spilling x30_0 to mem
mulx r12, rdi, rbx; x53_1, x53_0<- arg1[0] * x3 (_0*_0)
mov rdx, rbp; x16 to rdx
mulx rbx, rbp, [ rsi + 0x0 ]; x60_1, x60_0<- arg1[0] * x16 (_0*_0)
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x88 ], r12; spilling x53_1 to mem
mov [ rsp + 0x90 ], rdi; spilling x53_0 to mem
mulx rdi, r12, rax; x18_1, x18_0<- arg1[7] * x10001 (_0*_0)
mov rdx, rax; x10001 to rdx
mov [ rsp + 0x98 ], rbx; spilling x60_1 to mem
mulx rbx, rax, [ rsi + 0x30 ]; x20_1, x20_0<- arg1[6] * x10001 (_0*_0)
mov [ rsp + 0xa8 ], rdi; spilling x18_1 to mem
mov rdi, rbx;x10020_1, copying x20_1 here, cause x20_1 is needed in a reg. It has those deps: "", current hard deps: "x20_0, x20_1"
mov [ rsp + 0xa0 ], rbp; spilling x60_0 to mem
xor rbp, rbp
adox r10, rax
adox rdi, r15
xchg rdx, r11; x10003, swapping with x10001, which is currently in rdx
mulx rax, r15, [ rsi + 0x30 ]; x21_1, x21_0<- arg1[6] * x10003 (_0*_0)
mov rbx, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0xb0 ], rdi; spilling x10020_1 to mem
mulx rdi, rbp, r11; x23_1, x23_0<- arg1[5] * x10001 (_0*_0)
mov rdx, rdi;x10023_1, copying x23_1 here, cause x23_1 is needed in a reg. It has those deps: "", current hard deps: "x23_0, x23_1"
adcx r15, rbp
adcx rdx, rax
xchg rdx, rbx; x10003, swapping with x10023_1, which is currently in rdx
mulx rbp, rax, [ rsi + 0x28 ]; x24_1, x24_0<- arg1[5] * x10003 (_0*_0)
mov [ rsp + 0xb8 ], rbx; spilling x10023_1 to mem
mov rbx, rbp;x10026_1, copying x24_1 here, cause x24_1 is needed in a reg. It has those deps: "", current hard deps: "x24_0, x24_1"
xor rdi, rdi
adox r8, rax
adox rbx, rcx
mov rcx, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rbp, rax, r13; x25_1, x25_0<- arg1[5] * x10005 (_0*_0)
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0xc0 ], r15; spilling x10023_0 to mem
mulx r15, rdi, r11; x27_1, x27_0<- arg1[4] * x10001 (_0*_0)
mov rdx, r15;x10027_1, copying x27_1 here, cause x27_1 is needed in a reg. It has those deps: "", current hard deps: "x27_0, x27_1"
adcx r8, rdi
adcx rdx, rbx
mov rbx, rdx; preserving value of x10027_1 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r15, rdi, rcx; x28_1, x28_0<- arg1[4] * x10003 (_0*_0)
mov rdx, r15;x10029_1, copying x28_1 here, cause x28_1 is needed in a reg. It has those deps: "", current hard deps: "x28_0, x28_1"
add rax, rdi; could be done better, if r0 has been u8 as well
adcx rdx, rbp
xchg rdx, r13; x10005, swapping with x10029_1, which is currently in rdx
mulx rdi, rbp, [ rsi + 0x20 ]; x29_1, x29_0<- arg1[4] * x10005 (_0*_0)
mov r15, rdi;x10032_1, copying x29_1 here, cause x29_1 is needed in a reg. It has those deps: "", current hard deps: "x29_0, x29_1"
add r9, rbp; could be done better, if r0 has been u8 as well
adcx r15, r14
mulx rbp, r14, [ rsi + 0x18 ]; x34_1, x34_0<- arg1[3] * x10005 (_0*_0)
mov rdi, rbp;x10008_1, copying x34_1 here, cause x34_1 is needed in a reg. It has those deps: "", current hard deps: "x34_0, x34_1"
mov rdx, r14;x10008_0, copying x34_0 here, cause x34_0 is needed in a reg. It has those deps: "", current hard deps: "x34_0, x34_1"
add rdx, [ rsp + 0x80 ]; could be done better, if r0 has been u8 as well
adcx rdi, [ rsp + 0x78 ]
mov r14, rdx; preserving value of x10008_0 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0xc8 ], rbx; spilling x10027_1 to mem
mulx rbx, rbp, rdx; x31_1, x31_0<- arg1[4]^2
mov rdx, r11; x10001 to rdx
mov [ rsp + 0xd0 ], r8; spilling x10027_0 to mem
mulx r8, r11, [ rsi + 0x18 ]; x32_1, x32_0<- arg1[3] * x10001 (_0*_0)
mov [ rsp + 0xd8 ], r10; spilling x10020_0 to mem
mov r10, r8;x10030_1, copying x32_1 here, cause x32_1 is needed in a reg. It has those deps: "", current hard deps: "x32_0, x32_1"
test al, al
adox rax, r11
adox r10, r13
xchg rdx, rcx; x10003, swapping with x10001, which is currently in rdx
mulx r11, r13, [ rsi + 0x18 ]; x33_1, x33_0<- arg1[3] * x10003 (_0*_0)
mov r8, r11;x10033_1, copying x33_1 here, cause x33_1 is needed in a reg. It has those deps: "", current hard deps: "x33_0, x33_1"
adcx r9, r13
adcx r8, r15
mulx r13, r15, [ rsi + 0x10 ]; x39_1, x39_0<- arg1[2] * x10003 (_0*_0)
mov rdx, r13;x10009_1, copying x39_1 here, cause x39_1 is needed in a reg. It has those deps: "", current hard deps: "x39_0, x39_1"
add r14, r15; could be done better, if r0 has been u8 as well
adcx rdx, rdi
mov rdi, rdx; preserving value of x10009_1 into a new reg
mov rdx, [ rsp + 0x70 ]; saving x13 in rdx.
mulx r15, r11, [ rsi + 0x18 ]; x36_1, x36_0<- arg1[3] * x13 (_0*_0)
mov r13, rdx; preserving value of x13 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xe0 ], r10; spilling x10030_1 to mem
mov [ rsp + 0xe8 ], rax; spilling x10030_0 to mem
mulx rax, r10, [ rsp + 0x58 ]; x35_1, x35_0<- arg1[3] * x12 (_0*_0)
mov rdx, rax;x10011_1, copying x35_1 here, cause x35_1 is needed in a reg. It has those deps: "", current hard deps: "x35_0, x35_1"
test al, al
adox rbp, r10
adox rdx, rbx
mov r10, r15;x10014_1, copying x36_1 here, cause x36_1 is needed in a reg. It has those deps: "", current hard deps: "x36_0, x36_1"
mov rbx, r11;x10014_0, copying x36_0 here, cause x36_0 is needed in a reg. It has those deps: "", current hard deps: "x36_0, x36_1"
adcx rbx, [ rsp + 0x68 ]
adcx r10, [ rsp + 0x60 ]
mov r11, rdx; preserving value of x10011_1 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rax, r15, rdx; x37_1, x37_0<- arg1[3]^2
mov rdx, rax;x10017_1, copying x37_1 here, cause x37_1 is needed in a reg. It has those deps: "", current hard deps: "x37_0, x37_1"
add r12, r15; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0xa8 ]
xchg rdx, rcx; x10001, swapping with x10017_1, which is currently in rdx
mulx rax, r15, [ rsi + 0x10 ]; x38_1, x38_0<- arg1[2] * x10001 (_0*_0)
mov [ rsp + 0xf0 ], rcx; spilling x10017_1 to mem
mov rcx, rax;x10034_1, copying x38_1 here, cause x38_1 is needed in a reg. It has those deps: "", current hard deps: "x38_0, x38_1"
add r9, r15; could be done better, if r0 has been u8 as well
adcx rcx, r8
test al, al
adox r9, [ rsp + 0xa0 ]
adox rcx, [ rsp + 0x98 ]
mulx r15, r8, [ rsi + 0x8 ]; x45_1, x45_0<- arg1[1] * x10001 (_0*_0)
mov rdx, r13; x13 to rdx
mulx rax, r13, [ rsi + 0x10 ]; x42_1, x42_0<- arg1[2] * x13 (_0*_0)
mov [ rsp + 0xf8 ], rcx; spilling x72_1 to mem
mov rcx, r15;x10010_1, copying x45_1 here, cause x45_1 is needed in a reg. It has those deps: "", current hard deps: "x45_0, x45_1"
adcx r14, r8
adcx rcx, rdi
mov rdi, rdx; preserving value of x13 into a new reg
mov rdx, [ rsp + 0x50 ]; saving x9 in rdx.
mulx r15, r8, [ rsi + 0x10 ]; x40_1, x40_0<- arg1[2] * x9 (_0*_0)
mov [ rsp + 0x100 ], r9; spilling x72_0 to mem
mov r9, r15;x10012_1, copying x40_1 here, cause x40_1 is needed in a reg. It has those deps: "", current hard deps: "x40_0, x40_1"
add rbp, r8; could be done better, if r0 has been u8 as well
adcx r9, r11
mov r11, rdx; preserving value of x9 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r15, r8, [ rsp + 0x58 ]; x41_1, x41_0<- arg1[2] * x12 (_0*_0)
mov rdx, r15;x10015_1, copying x41_1 here, cause x41_1 is needed in a reg. It has those deps: "", current hard deps: "x41_0, x41_1"
test al, al
adox rbx, r8
adox rdx, r10
mov r10, rax;x10018_1, copying x42_1 here, cause x42_1 is needed in a reg. It has those deps: "", current hard deps: "x42_0, x42_1"
adcx r12, r13
adcx r10, [ rsp + 0xf0 ]
mov r13, rdx; preserving value of x10015_1 into a new reg
mov rdx, [ rsp + 0x40 ]; saving x14 in rdx.
mulx r8, rax, [ rsi + 0x10 ]; x43_1, x43_0<- arg1[2] * x14 (_0*_0)
mov [ rsp + 0x108 ], rcx; spilling x10010_1 to mem
mov rcx, r8;x10021_1, copying x43_1 here, cause x43_1 is needed in a reg. It has those deps: "", current hard deps: "x43_0, x43_1"
mov r15, rax;x10021_0, copying x43_0 here, cause x43_0 is needed in a reg. It has those deps: "", current hard deps: "x43_0, x43_1"
test al, al
adox r15, [ rsp + 0xd8 ]
adox rcx, [ rsp + 0xb0 ]
mov rax, rdx; preserving value of x14 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x110 ], r14; spilling x10010_0 to mem
mulx r14, r8, rdx; x44_1, x44_0<- arg1[2]^2
mov [ rsp + 0x118 ], rcx; spilling x10021_1 to mem
mov rcx, r14;x10024_1, copying x44_1 here, cause x44_1 is needed in a reg. It has those deps: "", current hard deps: "x44_0, x44_1"
mov rdx, r8;x10024_0, copying x44_0 here, cause x44_0 is needed in a reg. It has those deps: "", current hard deps: "x44_0, x44_1"
adcx rdx, [ rsp + 0xc0 ]
adcx rcx, [ rsp + 0xb8 ]
mov r8, rdx; preserving value of x10024_0 into a new reg
mov rdx, [ rsp + 0x38 ]; saving x6 in rdx.
mov [ rsp + 0x120 ], rcx; spilling x10024_1 to mem
mulx rcx, r14, [ rsi + 0x8 ]; x46_1, x46_0<- arg1[1] * x6 (_0*_0)
mov [ rsp + 0x130 ], r15; spilling x10021_0 to mem
mov r15, rcx;x10013_1, copying x46_1 here, cause x46_1 is needed in a reg. It has those deps: "", current hard deps: "x46_0, x46_1"
mov [ rsp + 0x128 ], r8; spilling x10024_0 to mem
xor r8, r8
adox rbp, r14
adox r15, r9
adcx rbp, [ rsp + 0x90 ]
adcx r15, [ rsp + 0x88 ]
mulx r14, r9, [ rsi + 0x0 ]; x54_1, x54_0<- arg1[0] * x6 (_0*_0)
mov rdx, r11; x9 to rdx
mulx rcx, r11, [ rsi + 0x8 ]; x47_1, x47_0<- arg1[1] * x9 (_0*_0)
mov r8, rcx;x10016_1, copying x47_1 here, cause x47_1 is needed in a reg. It has those deps: "", current hard deps: "x47_0, x47_1"
mov [ rsp + 0x138 ], r15; spilling x65_1 to mem
xor r15, r15
adox rbx, r11
adox r8, r13
mov r13, r14;x66_1, copying x54_1 here, cause x54_1 is needed in a reg. It has those deps: "", current hard deps: "x54_0, x54_1"
adcx rbx, r9
adcx r13, r8
mulx r14, r9, [ rsi + 0x0 ]; x55_1, x55_0<- arg1[0] * x9 (_0*_0)
mov rdx, [ rsp + 0x58 ]; x12 to rdx
mulx rcx, r11, [ rsi + 0x8 ]; x48_1, x48_0<- arg1[1] * x12 (_0*_0)
mov r8, rcx;x10019_1, copying x48_1 here, cause x48_1 is needed in a reg. It has those deps: "", current hard deps: "x48_0, x48_1"
add r12, r11; could be done better, if r0 has been u8 as well
adcx r8, r10
mov r10, r14;x67_1, copying x55_1 here, cause x55_1 is needed in a reg. It has those deps: "", current hard deps: "x55_0, x55_1"
test al, al
adox r12, r9
adox r10, r8
mulx r14, r9, [ rsi + 0x0 ]; x56_1, x56_0<- arg1[0] * x12 (_0*_0)
mov rdx, rdi; x13 to rdx
mulx r11, rdi, [ rsi + 0x8 ]; x49_1, x49_0<- arg1[1] * x13 (_0*_0)
mov r8, r11;x10022_1, copying x49_1 here, cause x49_1 is needed in a reg. It has those deps: "", current hard deps: "x49_0, x49_1"
mov rcx, rdi;x10022_0, copying x49_0 here, cause x49_0 is needed in a reg. It has those deps: "", current hard deps: "x49_0, x49_1"
adcx rcx, [ rsp + 0x130 ]
adcx r8, [ rsp + 0x118 ]
mov rdi, r14;x68_1, copying x56_1 here, cause x56_1 is needed in a reg. It has those deps: "", current hard deps: "x56_0, x56_1"
add rcx, r9; could be done better, if r0 has been u8 as well
adcx rdi, r8
mulx r14, r9, [ rsi + 0x0 ]; x57_1, x57_0<- arg1[0] * x13 (_0*_0)
mov rdx, rax; x14 to rdx
mulx r11, rax, [ rsi + 0x8 ]; x50_1, x50_0<- arg1[1] * x14 (_0*_0)
mov r15, r11;x10025_1, copying x50_1 here, cause x50_1 is needed in a reg. It has those deps: "", current hard deps: "x50_0, x50_1"
mov r8, rax;x10025_0, copying x50_0 here, cause x50_0 is needed in a reg. It has those deps: "", current hard deps: "x50_0, x50_1"
mov [ rsp + 0x140 ], rbp; spilling x65_0 to mem
xor rbp, rbp
adox r8, [ rsp + 0x128 ]
adox r15, [ rsp + 0x120 ]
mov rax, r14;x69_1, copying x57_1 here, cause x57_1 is needed in a reg. It has those deps: "", current hard deps: "x57_0, x57_1"
adcx r8, r9
adcx rax, r15
mulx r14, r9, [ rsi + 0x0 ]; x58_1, x58_0<- arg1[0] * x14 (_0*_0)
mov rdx, [ rsp + 0x48 ]; x15 to rdx
mulx r15, r11, [ rsi + 0x8 ]; x51_1, x51_0<- arg1[1] * x15 (_0*_0)
mov [ rsp + 0x150 ], rbx; spilling x66_0 to mem
mov rbx, r15;x10028_1, copying x51_1 here, cause x51_1 is needed in a reg. It has those deps: "", current hard deps: "x51_0, x51_1"
mov [ rsp + 0x148 ], r13; spilling x66_1 to mem
mov r13, r11;x10028_0, copying x51_0 here, cause x51_0 is needed in a reg. It has those deps: "", current hard deps: "x51_0, x51_1"
test al, al
adox r13, [ rsp + 0xd0 ]
adox rbx, [ rsp + 0xc8 ]
mov r11, r14;x70_1, copying x58_1 here, cause x58_1 is needed in a reg. It has those deps: "", current hard deps: "x58_0, x58_1"
adcx r13, r9
adcx r11, rbx
mulx r14, r9, [ rsi + 0x0 ]; x59_1, x59_0<- arg1[0] * x15 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rbx, r15, rdx; x52_1, x52_0<- arg1[1]^2
mov rbp, rbx;x10031_1, copying x52_1 here, cause x52_1 is needed in a reg. It has those deps: "", current hard deps: "x52_0, x52_1"
mov rdx, r15;x10031_0, copying x52_0 here, cause x52_0 is needed in a reg. It has those deps: "", current hard deps: "x52_0, x52_1"
mov [ rsp + 0x158 ], r10; spilling x67_1 to mem
xor r10, r10
adox rdx, [ rsp + 0xe8 ]
adox rbp, [ rsp + 0xe0 ]
mov r15, r14;x71_1, copying x59_1 here, cause x59_1 is needed in a reg. It has those deps: "", current hard deps: "x59_0, x59_1"
adcx rdx, r9
adcx r15, rbp
mov r9, rdx; preserving value of x71_0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx rbx, r14, rdx; x61_1, x61_0<- arg1[0]^2
mov rbp, rbx;x62_1, copying x61_1 here, cause x61_1 is needed in a reg. It has those deps: "", current hard deps: "x61_0, x61_1"
mov rdx, r14;x62_0, copying x61_0 here, cause x61_0 is needed in a reg. It has those deps: "", current hard deps: "x61_0, x61_1"
test al, al
adox rdx, [ rsp + 0x110 ]
adox rbp, [ rsp + 0x108 ]
mov r14, 0x3a ; moving imm to reg
bzhi rbx, rdx, r14; x64 <- x62_0 (only least 0x3a bits)
mov r10, rbp; hi x63_1<- x62_1
shrd rdx, r10, 58; lo
shr r10, 58; x63_1>>=58
mov [ rsp + 0x160 ], rbx; spilling x64 to mem
mov rbx, r10;x73_1, copying x63_1 here, cause x63_1 is needed in a reg. It has those deps: "", current hard deps: "x63_0, x63_1"
mov rbp, rdx;x73_0, copying x63_0 here, cause x63_0 is needed in a reg. It has those deps: "", current hard deps: "x63_0, x63_1"
xor r14, r14
adox rbp, [ rsp + 0x100 ]
adox rbx, [ rsp + 0xf8 ]
mov rdx, 0x3a ; moving imm to reg
bzhi r10, rbp, rdx; x75 <- x73_0 (only least 0x3a bits)
mov r14, rbx; hi x74_1<- x73_1
shrd rbp, r14, 58; lo
shr r14, 58; x74_1>>=58
mov rdx, r14;x76_1, copying x74_1 here, cause x74_1 is needed in a reg. It has those deps: "", current hard deps: "x74_0, x74_1"
xor rbx, rbx
adox r9, rbp
adox rdx, r15
mov r15, 0x3ffffffffffffff ; moving imm to reg
mov rbp, r9;x78, copying x76_0 here, cause x76_0 is needed in a reg. It has those deps: "x77_0, x77_1, x78, size: 3", current hard deps: ""
and rbp, r15; x78 <- x76_0&0x3ffffffffffffff
mov r14, rdx; hi x77_1<- x76_1
shrd r9, r14, 58; lo
shr r14, 58; x77_1>>=58
mov rdx, r14;x79_1, copying x77_1 here, cause x77_1 is needed in a reg. It has those deps: "", current hard deps: "x77_0, x77_1"
test al, al
adox r13, r9
adox rdx, r11
mov r11, r13;x81, copying x79_0 here, cause x79_0 is needed in a reg. It has those deps: "x80_0, x80_1, x81, size: 3", current hard deps: ""
and r11, r15; x81 <- x79_0&0x3ffffffffffffff
mov r9, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ r9 + 0x18 ], r11; out1[3] = x81
mov r14, rdx; hi x80_1<- x79_1
shrd r13, r14, 58; lo
shr r14, 58; x80_1>>=58
mov rdx, r14;x82_1, copying x80_1 here, cause x80_1 is needed in a reg. It has those deps: "", current hard deps: "x80_0, x80_1"
test al, al
adox r8, r13
adox rdx, rax
mov rax, r8;x84, copying x82_0 here, cause x82_0 is needed in a reg. It has those deps: "x83_0, x83_1, x84, size: 3", current hard deps: ""
and rax, r15; x84 <- x82_0&0x3ffffffffffffff
mov r11, rdx; hi x83_1<- x82_1
shrd r8, r11, 58; lo
shr r11, 58; x83_1>>=58
mov [ r9 + 0x20 ], rax; out1[4] = x84
mov r13, r11;x85_1, copying x83_1 here, cause x83_1 is needed in a reg. It has those deps: "", current hard deps: "x83_0, x83_1"
test al, al
adox rcx, r8
adox r13, rdi
mov rdi, rcx;x87, copying x85_0 here, cause x85_0 is needed in a reg. It has those deps: "x86_0, x86_1, x87, size: 3", current hard deps: ""
and rdi, r15; x87 <- x85_0&0x3ffffffffffffff
mov [ r9 + 0x28 ], rdi; out1[5] = x87
mov r14, r13; hi x86_1<- x85_1
shrd rcx, r14, 58; lo
shr r14, 58; x86_1>>=58
mov rdx, r14;x88_1, copying x86_1 here, cause x86_1 is needed in a reg. It has those deps: "", current hard deps: "x86_0, x86_1"
add r12, rcx; could be done better, if r0 has been u8 as well
adcx rdx, [ rsp + 0x158 ]
mov rax, r12;x90, copying x88_0 here, cause x88_0 is needed in a reg. It has those deps: "x89_0, x89_1, x90, size: 3", current hard deps: ""
and rax, r15; x90 <- x88_0&0x3ffffffffffffff
mov [ r9 + 0x30 ], rax; out1[6] = x90
mov r8, rdx; hi x89_1<- x88_1
shrd r12, r8, 58; lo
shr r8, 58; x89_1>>=58
mov rbx, r8;x91_1, copying x89_1 here, cause x89_1 is needed in a reg. It has those deps: "", current hard deps: "x89_0, x89_1"
mov r11, r12;x91_0, copying x89_0 here, cause x89_0 is needed in a reg. It has those deps: "", current hard deps: "x89_0, x89_1"
xor r13, r13
adox r11, [ rsp + 0x150 ]
adox rbx, [ rsp + 0x148 ]
mov rdi, r11;x92_0, copying x91_0 here, cause x91_0 is needed in a reg. It has those deps: "x92_0, x92_1, x93, size: 3", current hard deps: ""
mov rcx, rbx; hi x92_1<- x91_1
shrd rdi, rcx, 58; lo
shr rcx, 58; x92_1>>=58
and r11, r15; x93 <- x91_0&0x3ffffffffffffff
mov [ r9 + 0x38 ], r11; out1[7] = x93
mov rdx, rcx;x94_1, copying x92_1 here, cause x92_1 is needed in a reg. It has those deps: "", current hard deps: "x92_0, x92_1"
mov r14, rdi;x94_0, copying x92_0 here, cause x92_0 is needed in a reg. It has those deps: "", current hard deps: "x92_0, x92_1"
adox r14, [ rsp + 0x140 ]
adox rdx, [ rsp + 0x138 ]
mov rax, 0x39 ; moving imm to reg
bzhi r12, r14, rax; x96 <- x94_0 (only least 0x39 bits)
mov [ r9 + 0x40 ], r12; out1[8] = x96
mov r8, rdx; hi x95_1<- x94_1
shrd r14, r8, 57; lo
shr r8, 57; x95_1>>=57
test al, al
adox r14, [ rsp + 0x160 ]
adox r8, r13
mov rbx, r14;x98, copying x97_0 here, cause x97_0 is needed in a reg. It has those deps: "x98, x99, size: 2", current hard deps: ""
shrd rbx, r8, 58; x98 <- x97_1||x97_0 >> 58
and r14, r15; x99 <- x97_0&0x3ffffffffffffff
lea rbx, [ rbx + r10 ]
mov [ r9 + 0x0 ], r14; out1[0] = x99
mov r10, rbx;x101, copying x100 here, cause x100 is needed in a reg. It has those deps: "x101, x102, size: 2", current hard deps: ""
shr r10, 58; x101 <- x100>> 58
lea r10, [ r10 + rbp ]
mov [ r9 + 0x10 ], r10; out1[2] = x103
and rbx, r15; x102 <- x100&0x3ffffffffffffff
mov [ r9 + 0x8 ], rbx; out1[1] = x102
mov rbx, [ rsp + 0x0 ] ; pop
mov rbp, [ rsp + 0x8 ] ; pop
mov r12, [ rsp + 0x10 ] ; pop
mov r13, [ rsp + 0x18 ] ; pop
mov r14, [ rsp + 0x20 ] ; pop
mov r15, [ rsp + 0x28 ] ; pop
add rsp, 0x168 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 1.1311
; seed 1785685356 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2333 ms / 50 evals=> 46.66ms/eval
; Time spent for assembling and measureing (initial batch_size=40, initial num_batches=31): 85 ms
; number of used evaluations: 50
; Ratio (time for assembling + measure)/(total runtime for 50 evals): 0.036433776253750536
; number reverted permutation/ tried permutation: 15 / 20 =75.000%
; number reverted decision/ tried decision: 21 / 29 =72.414%
