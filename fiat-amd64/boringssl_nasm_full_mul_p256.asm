default	rel

section	.text code align=64

ALIGN	64
$L$poly:
	DQ	0xffffffffffffffff,0x00000000ffffffff,0x0000000000000000,0xffffffff00000001


global	ecp_nistz256_mul_mont

ALIGN	32
ecp_nistz256_mul_mont:
	mov	QWORD[8+rsp],rdi	;WIN64 prologue
	mov	QWORD[16+rsp],rsi
	mov	rax,rsp
$L$SEH_begin_ecp_nistz256_mul_mont:
	mov	rdi,rcx
	mov	rsi,rdx
	mov	rdx,r8



	lea	rcx,[OPENSSL_ia32cap_P]
	mov	rcx,QWORD[8+rcx]
	and	ecx,0x80100
$L$mul_mont:
	push	rbp

	push	rbx

	push	r12

	push	r13

	push	r14

	push	r15

$L$mul_body:
	cmp	ecx,0x80100
	je	NEAR $L$mul_montx
	mov	rbx,rdx
	mov	rax,QWORD[rdx]
	mov	r9,QWORD[rsi]
	mov	r10,QWORD[8+rsi]
	mov	r11,QWORD[16+rsi]
	mov	r12,QWORD[24+rsi]

	call	__ecp_nistz256_mul_montq
	jmp	NEAR $L$mul_mont_done

ALIGN	32
$L$mul_montx:
	mov	rbx,rdx
	mov	rdx,QWORD[rdx]
	mov	r9,QWORD[rsi]
	mov	r10,QWORD[8+rsi]
	mov	r11,QWORD[16+rsi]
	mov	r12,QWORD[24+rsi]
	lea	rsi,[((-128))+rsi]

	call	__ecp_nistz256_mul_montx
$L$mul_mont_done:
	mov	r15,QWORD[rsp]

	mov	r14,QWORD[8+rsp]

	mov	r13,QWORD[16+rsp]

	mov	r12,QWORD[24+rsp]

	mov	rbx,QWORD[32+rsp]

	mov	rbp,QWORD[40+rsp]

	lea	rsp,[48+rsp]

$L$mul_epilogue:
	mov	rdi,QWORD[8+rsp]	;WIN64 epilogue
	mov	rsi,QWORD[16+rsp]
	DB	0F3h,0C3h		;repret

$L$SEH_end_ecp_nistz256_mul_mont:


ALIGN	32
__ecp_nistz256_mul_montq:



	mov	rbp,rax
	mul	r9
	mov	r14,QWORD[(($L$poly+8))]
	mov	r8,rax
	mov	rax,rbp
	mov	r9,rdx

	mul	r10
	mov	r15,QWORD[(($L$poly+24))]
	add	r9,rax
	mov	rax,rbp
	adc	rdx,0
	mov	r10,rdx

	mul	r11
	add	r10,rax
	mov	rax,rbp
	adc	rdx,0
	mov	r11,rdx

	mul	r12
	add	r11,rax
	mov	rax,r8
	adc	rdx,0
	xor	r13,r13
	mov	r12,rdx










	mov	rbp,r8
	shl	r8,32
	mul	r15
	shr	rbp,32
	add	r9,r8
	adc	r10,rbp
	adc	r11,rax
	mov	rax,QWORD[8+rbx]
	adc	r12,rdx
	adc	r13,0
	xor	r8,r8



	mov	rbp,rax
	mul	QWORD[rsi]
	add	r9,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[8+rsi]
	add	r10,rcx
	adc	rdx,0
	add	r10,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[16+rsi]
	add	r11,rcx
	adc	rdx,0
	add	r11,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[24+rsi]
	add	r12,rcx
	adc	rdx,0
	add	r12,rax
	mov	rax,r9
	adc	r13,rdx
	adc	r8,0



	mov	rbp,r9
	shl	r9,32
	mul	r15
	shr	rbp,32
	add	r10,r9
	adc	r11,rbp
	adc	r12,rax
	mov	rax,QWORD[16+rbx]
	adc	r13,rdx
	adc	r8,0
	xor	r9,r9



	mov	rbp,rax
	mul	QWORD[rsi]
	add	r10,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[8+rsi]
	add	r11,rcx
	adc	rdx,0
	add	r11,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[16+rsi]
	add	r12,rcx
	adc	rdx,0
	add	r12,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[24+rsi]
	add	r13,rcx
	adc	rdx,0
	add	r13,rax
	mov	rax,r10
	adc	r8,rdx
	adc	r9,0



	mov	rbp,r10
	shl	r10,32
	mul	r15
	shr	rbp,32
	add	r11,r10
	adc	r12,rbp
	adc	r13,rax
	mov	rax,QWORD[24+rbx]
	adc	r8,rdx
	adc	r9,0
	xor	r10,r10



	mov	rbp,rax
	mul	QWORD[rsi]
	add	r11,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[8+rsi]
	add	r12,rcx
	adc	rdx,0
	add	r12,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[16+rsi]
	add	r13,rcx
	adc	rdx,0
	add	r13,rax
	mov	rax,rbp
	adc	rdx,0
	mov	rcx,rdx

	mul	QWORD[24+rsi]
	add	r8,rcx
	adc	rdx,0
	add	r8,rax
	mov	rax,r11
	adc	r9,rdx
	adc	r10,0



	mov	rbp,r11
	shl	r11,32
	mul	r15
	shr	rbp,32
	add	r12,r11
	adc	r13,rbp
	mov	rcx,r12
	adc	r8,rax
	adc	r9,rdx
	mov	rbp,r13
	adc	r10,0



	sub	r12,-1
	mov	rbx,r8
	sbb	r13,r14
	sbb	r8,0
	mov	rdx,r9
	sbb	r9,r15
	sbb	r10,0

	cmovc	r12,rcx
	cmovc	r13,rbp
	mov	QWORD[rdi],r12
	cmovc	r8,rbx
	mov	QWORD[8+rdi],r13
	cmovc	r9,rdx
	mov	QWORD[16+rdi],r8
	mov	QWORD[24+rdi],r9

	DB	0F3h,0C3h		;repret


ALIGN	32
__ecp_nistz256_mul_montx:



	mulx	r9,r8,r9
	mulx	r10,rcx,r10
	mov	r14,32
	xor	r13,r13
	mulx	r11,rbp,r11
	mov	r15,QWORD[(($L$poly+24))]
	adc	r9,rcx
	mulx	r12,rcx,r12
	mov	rdx,r8
	adc	r10,rbp
	shlx	rbp,r8,r14
	adc	r11,rcx
	shrx	rcx,r8,r14
	adc	r12,0



	add	r9,rbp
	adc	r10,rcx

	mulx	rbp,rcx,r15
	mov	rdx,QWORD[8+rbx]
	adc	r11,rcx
	adc	r12,rbp
	adc	r13,0
	xor	r8,r8



	mulx	rbp,rcx,QWORD[((0+128))+rsi]
	adcx	r9,rcx
	adox	r10,rbp

	mulx	rbp,rcx,QWORD[((8+128))+rsi]
	adcx	r10,rcx
	adox	r11,rbp

	mulx	rbp,rcx,QWORD[((16+128))+rsi]
	adcx	r11,rcx
	adox	r12,rbp

	mulx	rbp,rcx,QWORD[((24+128))+rsi]
	mov	rdx,r9
	adcx	r12,rcx
	shlx	rcx,r9,r14
	adox	r13,rbp
	shrx	rbp,r9,r14

	adcx	r13,r8
	adox	r8,r8
	adc	r8,0



	add	r10,rcx
	adc	r11,rbp

	mulx	rbp,rcx,r15
	mov	rdx,QWORD[16+rbx]
	adc	r12,rcx
	adc	r13,rbp
	adc	r8,0
	xor	r9,r9



	mulx	rbp,rcx,QWORD[((0+128))+rsi]
	adcx	r10,rcx
	adox	r11,rbp

	mulx	rbp,rcx,QWORD[((8+128))+rsi]
	adcx	r11,rcx
	adox	r12,rbp

	mulx	rbp,rcx,QWORD[((16+128))+rsi]
	adcx	r12,rcx
	adox	r13,rbp

	mulx	rbp,rcx,QWORD[((24+128))+rsi]
	mov	rdx,r10
	adcx	r13,rcx
	shlx	rcx,r10,r14
	adox	r8,rbp
	shrx	rbp,r10,r14

	adcx	r8,r9
	adox	r9,r9
	adc	r9,0



	add	r11,rcx
	adc	r12,rbp

	mulx	rbp,rcx,r15
	mov	rdx,QWORD[24+rbx]
	adc	r13,rcx
	adc	r8,rbp
	adc	r9,0
	xor	r10,r10



	mulx	rbp,rcx,QWORD[((0+128))+rsi]
	adcx	r11,rcx
	adox	r12,rbp

	mulx	rbp,rcx,QWORD[((8+128))+rsi]
	adcx	r12,rcx
	adox	r13,rbp

	mulx	rbp,rcx,QWORD[((16+128))+rsi]
	adcx	r13,rcx
	adox	r8,rbp

	mulx	rbp,rcx,QWORD[((24+128))+rsi]
	mov	rdx,r11
	adcx	r8,rcx
	shlx	rcx,r11,r14
	adox	r9,rbp
	shrx	rbp,r11,r14

	adcx	r9,r10
	adox	r10,r10
	adc	r10,0



	add	r12,rcx
	adc	r13,rbp

	mulx	rbp,rcx,r15
	mov	rbx,r12
	mov	r14,QWORD[(($L$poly+8))]
	adc	r8,rcx
	mov	rdx,r13
	adc	r9,rbp
	adc	r10,0



	xor	eax,eax
	mov	rcx,r8
	sbb	r12,-1
	sbb	r13,r14
	sbb	r8,0
	mov	rbp,r9
	sbb	r9,r15
	sbb	r10,0

	cmovc	r12,rbx
	cmovc	r13,rdx
	mov	QWORD[rdi],r12
	cmovc	r8,rcx
	mov	QWORD[8+rdi],r13
	cmovc	r9,rbp
	mov	QWORD[16+rdi],r8
	mov	QWORD[24+rdi],r9

	DB	0F3h,0C3h		;repret
