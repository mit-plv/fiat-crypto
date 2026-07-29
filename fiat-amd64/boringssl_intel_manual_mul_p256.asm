SECTION .text
	GLOBAL ecp_nistz256_mul_mont
ecp_nistz256_mul_mont:
push   rbp
push   rbx
push   r12
push   r13
push   r14
push   r15
xchg   rdx,rsi                  ; hack: swap args
mov    rbx,rdx
mov    rax,QWORD PTR [rbx]
mov    r9,QWORD PTR [rsi]
mov    r10,QWORD PTR [rsi+0x8]
mov    r11,QWORD PTR [rsi+0x10]
mov    r12,QWORD PTR [rsi+0x18]
mov    rbp,rax
mul    r9
mov    r14,0x00000000ffffffff
mov    r8,rax
mov    rax,rbp
mov    r9,rdx
mul    r10
mov    r15,0xffffffff00000001
add    r9,rax
mov    rax,rbp
adc    rdx,0x0
mov    r10,rdx
mul    r11
add    r10,rax
mov    rax,rbp
adc    rdx,0x0
mov    r11,rdx
mul    r12
add    r11,rax
mov    rax,r8
adc    rdx,0x0
xor    r13,r13
mov    r12,rdx
mov    rbp,r8
shl    r8,0x20
mul    r15
shr    rbp,0x20
add    r9,r8
adc    r10,rbp
adc    r11,rax
mov    rax,QWORD PTR [rbx+0x8]
adc    r12,rdx
adc    r13,0x0
xor    r8,r8
mov    rbp,rax
mul    QWORD PTR [rsi]
add    r9,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x8]
add    r10,rcx
adc    rdx,0x0
add    r10,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x10]
add    r11,rcx
adc    rdx,0x0
add    r11,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x18]
add    r12,rcx
adc    rdx,0x0
add    r12,rax
mov    rax,r9
adc    r13,rdx
adc    r8,0x0
mov    rbp,r9
shl    r9,0x20
mul    r15
shr    rbp,0x20
add    r10,r9
adc    r11,rbp
adc    r12,rax
mov    rax,QWORD PTR [rbx+0x10]
adc    r13,rdx
adc    r8,0x0
xor    r9,r9
mov    rbp,rax
mul    QWORD PTR [rsi]
add    r10,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x8]
add    r11,rcx
adc    rdx,0x0
add    r11,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x10]
add    r12,rcx
adc    rdx,0x0
add    r12,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x18]
add    r13,rcx
adc    rdx,0x0
add    r13,rax
mov    rax,r10
adc    r8,rdx
adc    r9,0x0
mov    rbp,r10
shl    r10,0x20
mul    r15
shr    rbp,0x20
add    r11,r10
adc    r12,rbp
adc    r13,rax
mov    rax,QWORD PTR [rbx+0x18]
adc    r8,rdx
adc    r9,0x0
xor    r10,r10
mov    rbp,rax
mul    QWORD PTR [rsi]
add    r11,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x8]
add    r12,rcx
adc    rdx,0x0
add    r12,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x10]
add    r13,rcx
adc    rdx,0x0
add    r13,rax
mov    rax,rbp
adc    rdx,0x0
mov    rcx,rdx
mul    QWORD PTR [rsi+0x18]
add    r8,rcx
adc    rdx,0x0
add    r8,rax
mov    rax,r11
adc    r9,rdx
adc    r10,0x0
mov    rbp,r11
shl    r11,0x20
mul    r15
shr    rbp,0x20
add    r12,r11
adc    r13,rbp
mov    rcx,r12
adc    r8,rax
adc    r9,rdx
mov    rbp,r13
adc    r10,0x0
sub    r12,0xffffffffffffffff
mov    rbx,r8
sbb    r13,r14
sbb    r8,0x0
mov    rdx,r9
sbb    r9,r15
sbb    r10,0x0
cmovb  r12,rcx
cmovb  r13,rbp
mov    QWORD PTR [rdi],r12
cmovb  r8,rbx
mov    QWORD PTR [rdi+0x8],r13
cmovb  r9,rdx
mov    QWORD PTR [rdi+0x10],r8
mov    QWORD PTR [rdi+0x18],r9
mov    r15,QWORD PTR [rsp]
mov    r14,QWORD PTR [rsp+0x8]
mov    r13,QWORD PTR [rsp+0x10]
mov    r12,QWORD PTR [rsp+0x18]
mov    rbx,QWORD PTR [rsp+0x20]
mov    rbp,QWORD PTR [rsp+0x28]
lea    rsp,[rsp+0x30]
ret
