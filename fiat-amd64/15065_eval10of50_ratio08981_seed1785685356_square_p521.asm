SECTION .text
	GLOBAL square_p521
square_p521:
sub rsp, 0x150
mov [ rsp + 0x18 ], r13; spilling calSv-r13 to mem
mov [ rsp + 0x20 ], r14; spilling calSv-r14 to mem

;works
;imul r13, [ rsi + 0x28 ], 0x2; x11 <- arg1[5] * 0x2
;imul r14, r13, 0x2; x10007 <- x11 * 0x2

;does not work
imul r14, [ rsi + 0x28 ], 0x4; x11 <- arg1[5] * 0x2

imul rax, [ rsi + 0x40 ], 0x2; x3 <- arg1[8] * 0x2
imul r10, [ rsi + 0x40 ], 0x2; x10000 <- arg1[8] * 0x2
imul r11, [ rsi + 0x38 ], 0x2; x10002 <- arg1[7] * 0x2
imul rdx, [ rsi + 0x30 ], 0x2; x10004 <- arg1[6] * 0x2
imul rcx, [ rsi + 0x28 ], 0x2; x10006 <- arg1[5] * 0x2
imul r8, [ rsi + 0x40 ], 0x2; x2 <- arg1[8] * 0x2
imul r9, r8, 0x2; x10001 <- x2 * 0x2
imul r8, [ rsi + 0x38 ], 0x2; x5 <- arg1[7] * 0x2
mov [ rsp + 0x0 ], rbx; spilling calSv-rbx to mem
imul rbx, r8, 0x2; x10003 <- x5 * 0x2
imul r8, [ rsi + 0x38 ], 0x2; x6 <- arg1[7] * 0x2
mov [ rsp + 0x8 ], rbp; spilling calSv-rbp to mem
imul rbp, [ rsi + 0x30 ], 0x2; x8 <- arg1[6] * 0x2
mov [ rsp + 0x10 ], r12; spilling calSv-r12 to mem
imul r12, rbp, 0x2; x10005 <- x8 * 0x2
imul rbp, [ rsi + 0x30 ], 0x2; x9 <- arg1[6] * 0x2
imul r13, [ rsi + 0x28 ], 0x2; x12 <- arg1[5] * 0x2
mov [ rsp + 0x28 ], r15; spilling calSv-r15 to mem
imul r15, [ rsi + 0x20 ], 0x2; x13 <- arg1[4] * 0x2
mov [ rsp + 0x30 ], rdi; spilling out1 to mem
imul rdi, [ rsi + 0x18 ], 0x2; x14 <- arg1[3] * 0x2
mov [ rsp + 0x38 ], r8; spilling x6 to mem
imul r8, [ rsi + 0x10 ], 0x2; x15 <- arg1[2] * 0x2
mov [ rsp + 0x40 ], r8; spilling x15 to mem
imul r8, [ rsi + 0x8 ], 0x2; x16 <- arg1[1] * 0x2
xchg rdx, r10; x10000, swapping with x10004, which is currently in rdx
mov [ rsp + 0x48 ], rdi; spilling x14 to mem
mov [ rsp + 0x50 ], rbp; spilling x9 to mem
mulx rbp, rdi, [ rsi + 0x40 ]; x17_1, x17_0<- arg1[8] * x10000 (_0*_0)
mov rdx, r11; x10002 to rdx
mov [ rsp + 0x58 ], rbp; spilling x17_1 to mem
mulx rbp, r11, [ rsi + 0x38 ]; x19_1, x19_0<- arg1[7] * x10002 (_0*_0)
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x60 ], rdi; spilling x17_0 to mem
mov [ rsp + 0x68 ], r15; spilling x13 to mem
mulx r15, rdi, r10; x22_1, x22_0<- arg1[6] * x10004 (_0*_0)
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x70 ], r13; spilling x12 to mem
mulx r13, r10, rcx; x26_1, x26_0<- arg1[5] * x10006 (_0*_0)
mov rdx, r14; x10007 to rdx
mulx rcx, r14, [ rsi + 0x20 ]; x30_1, x30_0<- arg1[4] * x10007 (_0*_0)
mov rdx, rax; x3 to rdx
mov [ rsp + 0x78 ], rcx; spilling x30_1 to mem
mulx rcx, rax, [ rsi + 0x0 ]; x53_1, x53_0<- arg1[0] * x3 (_0*_0)
mov rdx, r8; x16 to rdx
mov [ rsp + 0x80 ], rcx; spilling x53_1 to mem
mulx rcx, r8, [ rsi + 0x0 ]; x60_1, x60_0<- arg1[0] * x16 (_0*_0)
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x88 ], rax; spilling x53_0 to mem
mov [ rsp + 0x90 ], rcx; spilling x60_1 to mem
mulx rcx, rax, r9; x18_1, x18_0<- arg1[7] * x10001 (_0*_0)
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x98 ], r8; spilling x60_0 to mem
mov [ rsp + 0xa0 ], rcx; spilling x18_1 to mem
mulx rcx, r8, r9; x20_1, x20_0<- arg1[6] * x10001 (_0*_0)
mov rdx, rcx;x10020_1, copying x20_1 here, cause x20_1 is needed in a reg. It has those deps: "", current hard deps: "x20_0, x20_1"
add r11, r8; could be done better, if r0 has been u8 as well
adcx rdx, rbp
mov rbp, rdx; preserving value of x10020_1 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mulx rcx, r8, rbx; x21_1, x21_0<- arg1[6] * x10003 (_0*_0)
mov rdx, r9; x10001 to rdx
mov [ rsp + 0xa8 ], rbp; spilling x10020_1 to mem
mulx rbp, r9, [ rsi + 0x28 ]; x23_1, x23_0<- arg1[5] * x10001 (_0*_0)
mov [ rsp + 0xb0 ], r11; spilling x10020_0 to mem
mov r11, rbp;x10023_1, copying x23_1 here, cause x23_1 is needed in a reg. It has those deps: "", current hard deps: "x23_0, x23_1"
test al, al
adox r8, r9
adox r11, rcx
mov rcx, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mulx rbp, r9, rbx; x24_1, x24_0<- arg1[5] * x10003 (_0*_0)
mov rdx, rbp;x10026_1, copying x24_1 here, cause x24_1 is needed in a reg. It has those deps: "", current hard deps: "x24_0, x24_1"
adcx rdi, r9
adcx rdx, r15
xchg rdx, r12; x10005, swapping with x10026_1, which is currently in rdx
mulx r9, r15, [ rsi + 0x28 ]; x25_1, x25_0<- arg1[5] * x10005 (_0*_0)
mov rbp, rdx; preserving value of x10005 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0xb8 ], r11; spilling x10023_1 to mem
mov [ rsp + 0xc0 ], r8; spilling x10023_0 to mem
mulx r8, r11, rcx; x27_1, x27_0<- arg1[4] * x10001 (_0*_0)
mov [ rsp + 0xc8 ], rax; spilling x18_0 to mem
mov rax, r8;x10027_1, copying x27_1 here, cause x27_1 is needed in a reg. It has those deps: "", current hard deps: "x27_0, x27_1"
xor rdx, rdx
adox rdi, r11
adox rax, r12
mov rdx, rbx; x10003 to rdx
mulx r12, rbx, [ rsi + 0x20 ]; x28_1, x28_0<- arg1[4] * x10003 (_0*_0)
mov r11, r12;x10029_1, copying x28_1 here, cause x28_1 is needed in a reg. It has those deps: "", current hard deps: "x28_0, x28_1"
adcx r15, rbx
adcx r11, r9
mov r9, rdx; preserving value of x10003 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx rbx, r8, rbp; x29_1, x29_0<- arg1[4] * x10005 (_0*_0)
mov rdx, rbx;x10032_1, copying x29_1 here, cause x29_1 is needed in a reg. It has those deps: "", current hard deps: "x29_0, x29_1"
test al, al
adox r10, r8
adox rdx, r13
xchg rdx, rbp; x10005, swapping with x10032_1, which is currently in rdx
mulx r12, r13, [ rsi + 0x18 ]; x34_1, x34_0<- arg1[3] * x10005 (_0*_0)
mov rdx, r12;x10008_1, copying x34_1 here, cause x34_1 is needed in a reg. It has those deps: "", current hard deps: "x34_0, x34_1"
adcx r14, r13
adcx rdx, [ rsp + 0x78 ]
mov r8, rdx; preserving value of x10008_1 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r13, rbx, rdx; x31_1, x31_0<- arg1[4]^2
mov rdx, rcx; x10001 to rdx
mulx r12, rcx, [ rsi + 0x18 ]; x32_1, x32_0<- arg1[3] * x10001 (_0*_0)
mov [ rsp + 0xd0 ], rax; spilling x10027_1 to mem
mov rax, r12;x10030_1, copying x32_1 here, cause x32_1 is needed in a reg. It has those deps: "", current hard deps: "x32_0, x32_1"
test al, al
adox r15, rcx
adox rax, r11
mov r11, rdx; preserving value of x10001 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx r12, rcx, r9; x33_1, x33_0<- arg1[3] * x10003 (_0*_0)
mov rdx, r12;x10033_1, copying x33_1 here, cause x33_1 is needed in a reg. It has those deps: "", current hard deps: "x33_0, x33_1"
adcx r10, rcx
adcx rdx, rbp
mov rbp, rdx; preserving value of x10033_1 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r12, rcx, r9; x39_1, x39_0<- arg1[2] * x10003 (_0*_0)
mov rdx, r12;x10009_1, copying x39_1 here, cause x39_1 is needed in a reg. It has those deps: "", current hard deps: "x39_0, x39_1"
test al, al
adox r14, rcx
adox rdx, r8
mov r9, rdx; preserving value of x10009_1 into a new reg
mov rdx, [ rsp + 0x70 ]; saving x12 in rdx.
mulx rcx, r8, [ rsi + 0x18 ]; x35_1, x35_0<- arg1[3] * x12 (_0*_0)
mov r12, rcx;x10011_1, copying x35_1 here, cause x35_1 is needed in a reg. It has those deps: "", current hard deps: "x35_0, x35_1"
adcx rbx, r8
adcx r12, r13
mov r13, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mulx rcx, r8, [ rsp + 0x68 ]; x36_1, x36_0<- arg1[3] * x13 (_0*_0)
mov [ rsp + 0xd8 ], rax; spilling x10030_1 to mem
mov rax, rcx;x10014_1, copying x36_1 here, cause x36_1 is needed in a reg. It has those deps: "", current hard deps: "x36_0, x36_1"
mov rdx, r8;x10014_0, copying x36_0 here, cause x36_0 is needed in a reg. It has those deps: "", current hard deps: "x36_0, x36_1"
add rdx, [ rsp + 0x60 ]; could be done better, if r0 has been u8 as well
adcx rax, [ rsp + 0x58 ]
mov r8, rdx; preserving value of x10014_0 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0xe0 ], r15; spilling x10030_0 to mem
mulx r15, rcx, rdx; x37_1, x37_0<- arg1[3]^2
mov [ rsp + 0xe8 ], rdi; spilling x10027_0 to mem
mov rdi, r15;x10017_1, copying x37_1 here, cause x37_1 is needed in a reg. It has those deps: "", current hard deps: "x37_0, x37_1"
mov rdx, rcx;x10017_0, copying x37_0 here, cause x37_0 is needed in a reg. It has those deps: "", current hard deps: "x37_0, x37_1"
test al, al
adox rdx, [ rsp + 0xc8 ]
adox rdi, [ rsp + 0xa0 ]
mov rcx, rdx; preserving value of x10017_0 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0xf0 ], rdi; spilling x10017_1 to mem
mulx rdi, r15, r11; x38_1, x38_0<- arg1[2] * x10001 (_0*_0)
mov rdx, rdi;x10034_1, copying x38_1 here, cause x38_1 is needed in a reg. It has those deps: "", current hard deps: "x38_0, x38_1"
adcx r10, r15
adcx rdx, rbp
test al, al
adox r10, [ rsp + 0x98 ]
adox rdx, [ rsp + 0x90 ]
mov rbp, rdx; preserving value of x72_1 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mulx rdi, r15, r11; x45_1, x45_0<- arg1[1] * x10001 (_0*_0)
mov rdx, rdi;x10010_1, copying x45_1 here, cause x45_1 is needed in a reg. It has those deps: "", current hard deps: "x45_0, x45_1"
adcx r14, r15
adcx rdx, r9
mov r11, rdx; preserving value of x10010_1 into a new reg
mov rdx, [ rsp + 0x50 ]; saving x9 in rdx.
mulx r15, r9, [ rsi + 0x10 ]; x40_1, x40_0<- arg1[2] * x9 (_0*_0)
mov rdi, r15;x10012_1, copying x40_1 here, cause x40_1 is needed in a reg. It has those deps: "", current hard deps: "x40_0, x40_1"
test al, al
adox rbx, r9
adox rdi, r12
xchg rdx, r13; x12, swapping with x9, which is currently in rdx
mulx r9, r12, [ rsi + 0x10 ]; x41_1, x41_0<- arg1[2] * x12 (_0*_0)
mov r15, r9;x10015_1, copying x41_1 here, cause x41_1 is needed in a reg. It has those deps: "", current hard deps: "x41_0, x41_1"
adcx r8, r12
adcx r15, rax
mov rax, rdx; preserving value of x12 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r9, r12, [ rsp + 0x68 ]; x42_1, x42_0<- arg1[2] * x13 (_0*_0)
mov [ rsp + 0xf8 ], rbp; spilling x72_1 to mem
mov rbp, r9;x10018_1, copying x42_1 here, cause x42_1 is needed in a reg. It has those deps: "", current hard deps: "x42_0, x42_1"
xor rdx, rdx
adox rcx, r12
adox rbp, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mulx r9, r12, [ rsp + 0x48 ]; x43_1, x43_0<- arg1[2] * x14 (_0*_0)
mov [ rsp + 0x100 ], r10; spilling x72_0 to mem
mov r10, r9;x10021_1, copying x43_1 here, cause x43_1 is needed in a reg. It has those deps: "", current hard deps: "x43_0, x43_1"
mov rdx, r12;x10021_0, copying x43_0 here, cause x43_0 is needed in a reg. It has those deps: "", current hard deps: "x43_0, x43_1"
adcx rdx, [ rsp + 0xb0 ]
adcx r10, [ rsp + 0xa8 ]
mov r12, rdx; preserving value of x10021_0 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x108 ], r11; spilling x10010_1 to mem
mulx r11, r9, rdx; x44_1, x44_0<- arg1[2]^2
mov [ rsp + 0x110 ], r14; spilling x10010_0 to mem
mov r14, r11;x10024_1, copying x44_1 here, cause x44_1 is needed in a reg. It has those deps: "", current hard deps: "x44_0, x44_1"
mov rdx, r9;x10024_0, copying x44_0 here, cause x44_0 is needed in a reg. It has those deps: "", current hard deps: "x44_0, x44_1"
add rdx, [ rsp + 0xc0 ]; could be done better, if r0 has been u8 as well
adcx r14, [ rsp + 0xb8 ]
mov r9, rdx; preserving value of x10024_0 into a new reg
mov rdx, [ rsp + 0x38 ]; saving x6 in rdx.
mov [ rsp + 0x118 ], r14; spilling x10024_1 to mem
mulx r14, r11, [ rsi + 0x8 ]; x46_1, x46_0<- arg1[1] * x6 (_0*_0)
mov [ rsp + 0x120 ], r9; spilling x10024_0 to mem
mov r9, r14;x10013_1, copying x46_1 here, cause x46_1 is needed in a reg. It has those deps: "", current hard deps: "x46_0, x46_1"
test al, al
adox rbx, r11
adox r9, rdi
adcx rbx, [ rsp + 0x88 ]
adcx r9, [ rsp + 0x80 ]
mulx r11, rdi, [ rsi + 0x0 ]; x54_1, x54_0<- arg1[0] * x6 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x128 ], r9; spilling x65_1 to mem
mulx r9, r14, r13; x47_1, x47_0<- arg1[1] * x9 (_0*_0)
mov [ rsp + 0x130 ], rbx; spilling x65_0 to mem
mov rbx, r9;x10016_1, copying x47_1 here, cause x47_1 is needed in a reg. It has those deps: "", current hard deps: "x47_0, x47_1"
xor rdx, rdx
adox r8, r14
adox rbx, r15
mov r15, r11;x66_1, copying x54_1 here, cause x54_1 is needed in a reg. It has those deps: "", current hard deps: "x54_0, x54_1"
adcx r8, rdi
adcx r15, rbx
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mulx r11, rdi, r13; x55_1, x55_0<- arg1[0] * x9 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r14, r13, rax; x48_1, x48_0<- arg1[1] * x12 (_0*_0)
mov rdx, r14;x10019_1, copying x48_1 here, cause x48_1 is needed in a reg. It has those deps: "", current hard deps: "x48_0, x48_1"
add rcx, r13; could be done better, if r0 has been u8 as well
adcx rdx, rbp
mov r9, r11;x67_1, copying x55_1 here, cause x55_1 is needed in a reg. It has those deps: "", current hard deps: "x55_0, x55_1"
xor rbp, rbp
adox rcx, rdi
adox r9, rdx
mov rdx, rax; x12 to rdx
mulx rbx, rax, [ rsi + 0x0 ]; x56_1, x56_0<- arg1[0] * x12 (_0*_0)
mov rdx, [ rsp + 0x68 ]; x13 to rdx
mulx r11, rdi, [ rsi + 0x8 ]; x49_1, x49_0<- arg1[1] * x13 (_0*_0)
mov r13, r11;x10022_1, copying x49_1 here, cause x49_1 is needed in a reg. It has those deps: "", current hard deps: "x49_0, x49_1"
adcx r12, rdi
adcx r13, r10
mov rbp, rbx;x68_1, copying x56_1 here, cause x56_1 is needed in a reg. It has those deps: "", current hard deps: "x56_0, x56_1"
xor r10, r10
adox r12, rax
adox rbp, r13
mulx rax, r14, [ rsi + 0x0 ]; x57_1, x57_0<- arg1[0] * x13 (_0*_0)
mov rdx, [ rsp + 0x48 ]; x14 to rdx
mulx rdi, rbx, [ rsi + 0x8 ]; x50_1, x50_0<- arg1[1] * x14 (_0*_0)
mov r13, rdi;x10025_1, copying x50_1 here, cause x50_1 is needed in a reg. It has those deps: "", current hard deps: "x50_0, x50_1"
mov r11, rbx;x10025_0, copying x50_0 here, cause x50_0 is needed in a reg. It has those deps: "", current hard deps: "x50_0, x50_1"
adcx r11, [ rsp + 0x120 ]
adcx r13, [ rsp + 0x118 ]
mov r10, rax;x69_1, copying x57_1 here, cause x57_1 is needed in a reg. It has those deps: "", current hard deps: "x57_0, x57_1"
xor rbx, rbx
adox r11, r14
adox r10, r13
mulx rax, r14, [ rsi + 0x0 ]; x58_1, x58_0<- arg1[0] * x14 (_0*_0)
mov rdx, [ rsp + 0x40 ]; x15 to rdx
mulx r13, rdi, [ rsi + 0x8 ]; x51_1, x51_0<- arg1[1] * x15 (_0*_0)
mov [ rsp + 0x140 ], r8; spilling x66_0 to mem
mov r8, r13;x10028_1, copying x51_1 here, cause x51_1 is needed in a reg. It has those deps: "", current hard deps: "x51_0, x51_1"
mov [ rsp + 0x138 ], r15; spilling x66_1 to mem
mov r15, rdi;x10028_0, copying x51_0 here, cause x51_0 is needed in a reg. It has those deps: "", current hard deps: "x51_0, x51_1"
adcx r15, [ rsp + 0xe8 ]
adcx r8, [ rsp + 0xd0 ]
mov rdi, rax;x70_1, copying x58_1 here, cause x58_1 is needed in a reg. It has those deps: "", current hard deps: "x58_0, x58_1"
test al, al
adox r15, r14
adox rdi, r8
mulx rax, r14, [ rsi + 0x0 ]; x59_1, x59_0<- arg1[0] * x15 (_0*_0)
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx r8, r13, rdx; x52_1, x52_0<- arg1[1]^2
mov [ rsp + 0x148 ], r9; spilling x67_1 to mem
mov r9, r8;x10031_1, copying x52_1 here, cause x52_1 is needed in a reg. It has those deps: "", current hard deps: "x52_0, x52_1"
mov rdx, r13;x10031_0, copying x52_0 here, cause x52_0 is needed in a reg. It has those deps: "", current hard deps: "x52_0, x52_1"
adcx rdx, [ rsp + 0xe0 ]
adcx r9, [ rsp + 0xd8 ]
mov r13, rax;x71_1, copying x59_1 here, cause x59_1 is needed in a reg. It has those deps: "", current hard deps: "x59_0, x59_1"
add rdx, r14; could be done better, if r0 has been u8 as well
adcx r13, r9
mov r14, rdx; preserving value of x71_0 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r8, rax, rdx; x61_1, x61_0<- arg1[0]^2
mov r9, r8;x62_1, copying x61_1 here, cause x61_1 is needed in a reg. It has those deps: "", current hard deps: "x61_0, x61_1"
mov rdx, rax;x62_0, copying x61_0 here, cause x61_0 is needed in a reg. It has those deps: "", current hard deps: "x61_0, x61_1"
add rdx, [ rsp + 0x110 ]; could be done better, if r0 has been u8 as well
adcx r9, [ rsp + 0x108 ]
mov rax, 0x3a ; moving imm to reg
bzhi r8, rdx, rax; x64 <- x62_0 (only least 0x3a bits)
mov rbx, r9; hi x63_1<- x62_1
shrd rdx, rbx, 58; lo
shr rbx, 58; x63_1>>=58
mov rax, rbx;x73_1, copying x63_1 here, cause x63_1 is needed in a reg. It has those deps: "", current hard deps: "x63_0, x63_1"
mov r9, rdx;x73_0, copying x63_0 here, cause x63_0 is needed in a reg. It has those deps: "", current hard deps: "x63_0, x63_1"
add r9, [ rsp + 0x100 ]; could be done better, if r0 has been u8 as well
adcx rax, [ rsp + 0xf8 ]
mov rdx, 0x3ffffffffffffff ; moving imm to reg
mov rbx, r9;x75, copying x73_0 here, cause x73_0 is needed in a reg. It has those deps: "x74_0, x74_1, x75, size: 3", current hard deps: ""
and rbx, rdx; x75 <- x73_0&0x3ffffffffffffff
mov rdx, rax; hi x74_1<- x73_1
shrd r9, rdx, 58; lo
shr rdx, 58; x74_1>>=58
mov rax, rdx;x76_1, copying x74_1 here, cause x74_1 is needed in a reg. It has those deps: "", current hard deps: "x74_0, x74_1"
add r14, r9; could be done better, if r0 has been u8 as well
adcx rax, r13
mov r13, 0x3ffffffffffffff ; moving imm to reg
mov r9, r14;x78, copying x76_0 here, cause x76_0 is needed in a reg. It has those deps: "x77_0, x77_1, x78, size: 3", current hard deps: ""
and r9, r13; x78 <- x76_0&0x3ffffffffffffff
mov rdx, rax; hi x77_1<- x76_1
shrd r14, rdx, 58; lo
shr rdx, 58; x77_1>>=58
mov rax, rdx;x79_1, copying x77_1 here, cause x77_1 is needed in a reg. It has those deps: "", current hard deps: "x77_0, x77_1"
add r15, r14; could be done better, if r0 has been u8 as well
adcx rax, rdi
mov rdi, r15;x81, copying x79_0 here, cause x79_0 is needed in a reg. It has those deps: "x80_0, x80_1, x81, size: 3", current hard deps: ""
and rdi, r13; x81 <- x79_0&0x3ffffffffffffff
mov r14, [ rsp + 0x30 ]; load m64 out1 to register64
mov [ r14 + 0x18 ], rdi; out1[3] = x81
mov rdx, rax; hi x80_1<- x79_1
shrd r15, rdx, 58; lo
shr rdx, 58; x80_1>>=58
mov rax, rdx;x82_1, copying x80_1 here, cause x80_1 is needed in a reg. It has those deps: "", current hard deps: "x80_0, x80_1"
add r11, r15; could be done better, if r0 has been u8 as well
adcx rax, r10
mov r10, r11;x84, copying x82_0 here, cause x82_0 is needed in a reg. It has those deps: "x83_0, x83_1, x84, size: 3", current hard deps: ""
and r10, r13; x84 <- x82_0&0x3ffffffffffffff
mov [ r14 + 0x20 ], r10; out1[4] = x84
mov rdi, rax; hi x83_1<- x82_1
shrd r11, rdi, 58; lo
shr rdi, 58; x83_1>>=58
mov rdx, rdi;x85_1, copying x83_1 here, cause x83_1 is needed in a reg. It has those deps: "", current hard deps: "x83_0, x83_1"
xor r15, r15
adox r12, r11
adox rdx, rbp
mov rbp, r12;x87, copying x85_0 here, cause x85_0 is needed in a reg. It has those deps: "x86_0, x86_1, x87, size: 3", current hard deps: ""
and rbp, r13; x87 <- x85_0&0x3ffffffffffffff
mov [ r14 + 0x28 ], rbp; out1[5] = x87
mov rax, rdx; hi x86_1<- x85_1
shrd r12, rax, 58; lo
shr rax, 58; x86_1>>=58
mov r10, rax;x88_1, copying x86_1 here, cause x86_1 is needed in a reg. It has those deps: "", current hard deps: "x86_0, x86_1"
add rcx, r12; could be done better, if r0 has been u8 as well
adcx r10, [ rsp + 0x148 ]
mov r11, rcx;x90, copying x88_0 here, cause x88_0 is needed in a reg. It has those deps: "x89_0, x89_1, x90, size: 3", current hard deps: ""
and r11, r13; x90 <- x88_0&0x3ffffffffffffff
mov [ r14 + 0x30 ], r11; out1[6] = x90
mov rdi, r10; hi x89_1<- x88_1
shrd rcx, rdi, 58; lo
shr rdi, 58; x89_1>>=58
mov rbp, rdi;x91_1, copying x89_1 here, cause x89_1 is needed in a reg. It has those deps: "", current hard deps: "x89_0, x89_1"
mov rdx, rcx;x91_0, copying x89_0 here, cause x89_0 is needed in a reg. It has those deps: "", current hard deps: "x89_0, x89_1"
test al, al
adox rdx, [ rsp + 0x140 ]
adox rbp, [ rsp + 0x138 ]
mov r12, rdx;x93, copying x91_0 here, cause x91_0 is needed in a reg. It has those deps: "x92_0, x92_1, x93, size: 3", current hard deps: ""
and r12, r13; x93 <- x91_0&0x3ffffffffffffff
mov [ r14 + 0x38 ], r12; out1[7] = x93
mov rax, rbp; hi x92_1<- x91_1
shrd rdx, rax, 58; lo
shr rax, 58; x92_1>>=58
mov r11, rax;x94_1, copying x92_1 here, cause x92_1 is needed in a reg. It has those deps: "", current hard deps: "x92_0, x92_1"
mov r10, rdx;x94_0, copying x92_0 here, cause x92_0 is needed in a reg. It has those deps: "", current hard deps: "x92_0, x92_1"
add r10, [ rsp + 0x130 ]; could be done better, if r0 has been u8 as well
adcx r11, [ rsp + 0x128 ]
mov rcx, 0x1ffffffffffffff ; moving imm to reg
mov rdi, r10;x96, copying x94_0 here, cause x94_0 is needed in a reg. It has those deps: "x95_0, x95_1, x96, size: 3", current hard deps: ""
and rdi, rcx; x96 <- x94_0&0x1ffffffffffffff
mov [ r14 + 0x40 ], rdi; out1[8] = x96
mov rbp, r11; hi x95_1<- x94_1
shrd r10, rbp, 57; lo
shr rbp, 57; x95_1>>=57
xor r12, r12
adox r10, r8
adox rbp, r12
mov r15, r10;x98, copying x97_0 here, cause x97_0 is needed in a reg. It has those deps: "x98, x99, size: 2", current hard deps: ""
shrd r15, rbp, 58; x98 <- x97_1||x97_0 >> 58
and r10, r13; x99 <- x97_0&0x3ffffffffffffff
lea r15, [ r15 + rbx ]
mov [ r14 + 0x0 ], r10; out1[0] = x99
mov r8, r15;x101, copying x100 here, cause x100 is needed in a reg. It has those deps: "x101, x102, size: 2", current hard deps: ""
shr r8, 58; x101 <- x100>> 58
lea r8, [ r8 + r9 ]
mov [ r14 + 0x10 ], r8; out1[2] = x103
and r15, r13; x102 <- x100&0x3ffffffffffffff
mov [ r14 + 0x8 ], r15; out1[1] = x102
mov rbx, [ rsp + 0x0 ] ; pop
mov rbp, [ rsp + 0x8 ] ; pop
mov r12, [ rsp + 0x10 ] ; pop
mov r13, [ rsp + 0x18 ] ; pop
mov r14, [ rsp + 0x20 ] ; pop
mov r15, [ rsp + 0x28 ] ; pop
add rsp, 0x150 
ret
; cpu Intel(R) Core(TM) i5-8265U CPU @ 1.60GHz
; ratio 0.8981
; seed 1785685356 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; time needed: 2523 ms / 10 evals=> 252.3ms/eval
; Time spent for assembling and measureing (initial batch_size=35, initial num_batches=31): 53 ms
; number of used evaluations: 10
; Ratio (time for assembling + measure)/(total runtime for 10 evals): 0.02100673801030519
; number reverted permutation/ tried permutation: 6 / 6 =100.000%
; number reverted decision/ tried decision: 2 / 4 =50.000%
