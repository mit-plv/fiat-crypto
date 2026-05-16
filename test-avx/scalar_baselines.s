	.file	"scalar_wrappers.c"
	.text
	.p2align 4
	.globl	scalar_add4
	.type	scalar_add4, @function
scalar_add4:
.LFB2:
	.cfi_startproc
	endbr64
	movq	%rsi, %rcx
	movq	%rdi, %rax
	movq	8(%rdx), %r9
	movq	16(%rdx), %r8
	movq	24(%rdx), %rdi
	movq	(%rdx), %r10
	addq	8(%rsi), %r9
	addq	16(%rsi), %r8
	addq	24(%rsi), %rdi
	addq	(%rcx), %r10
	movq	32(%rdx), %rsi
	addq	32(%rcx), %rsi
	movq	%r10, (%rax)
	movq	%r9, 8(%rax)
	movq	%r8, 16(%rax)
	movq	%rdi, 24(%rax)
	movq	%rsi, 32(%rax)
	movq	48(%rdx), %r9
	movq	56(%rdx), %r8
	movq	64(%rdx), %rdi
	movq	72(%rdx), %rsi
	movq	40(%rdx), %r10
	addq	48(%rcx), %r9
	addq	64(%rcx), %rdi
	addq	72(%rcx), %rsi
	addq	40(%rcx), %r10
	addq	56(%rcx), %r8
	movq	%r10, 40(%rax)
	movq	%rdi, 64(%rax)
	movq	%rsi, 72(%rax)
	movq	%r9, 48(%rax)
	movq	%r8, 56(%rax)
	movq	88(%rdx), %r9
	addq	88(%rcx), %r9
	movq	96(%rdx), %r8
	movq	104(%rdx), %rdi
	movq	112(%rdx), %rsi
	movq	80(%rdx), %r10
	addq	96(%rcx), %r8
	addq	104(%rcx), %rdi
	addq	112(%rcx), %rsi
	addq	80(%rcx), %r10
	movq	%r9, 88(%rax)
	movq	%r10, 80(%rax)
	movq	%r8, 96(%rax)
	movq	%rdi, 104(%rax)
	movq	%rsi, 112(%rax)
	movq	128(%rdx), %r9
	movq	136(%rdx), %r8
	movq	144(%rdx), %rdi
	movq	152(%rdx), %rsi
	addq	128(%rcx), %r9
	movq	120(%rdx), %rdx
	addq	136(%rcx), %r8
	addq	144(%rcx), %rdi
	addq	152(%rcx), %rsi
	addq	120(%rcx), %rdx
	movq	%r9, 128(%rax)
	movq	%rdx, 120(%rax)
	movq	%r8, 136(%rax)
	movq	%rdi, 144(%rax)
	movq	%rsi, 152(%rax)
	ret
	.cfi_endproc
.LFE2:
	.size	scalar_add4, .-scalar_add4
	.p2align 4
	.globl	scalar_sub4
	.type	scalar_sub4, @function
scalar_sub4:
.LFB3:
	.cfi_startproc
	endbr64
	xorl	%r10d, %r10d
	leaq	40+bal.3(%rip), %r9
.L4:
	leaq	bal.3(%rip), %r8
	movq	%r10, %rcx
	.p2align 4,,10
	.p2align 3
.L5:
	movq	(%r8), %rax
	addq	$8, %r8
	subq	(%rdx,%rcx), %rax
	addq	(%rsi,%rcx), %rax
	movq	%rax, (%rdi,%rcx)
	addq	$8, %rcx
	cmpq	%r8, %r9
	jne	.L5
	addq	$40, %r10
	cmpq	$160, %r10
	jne	.L4
	ret
	.cfi_endproc
.LFE3:
	.size	scalar_sub4, .-scalar_sub4
	.p2align 4
	.globl	scalar_opp4
	.type	scalar_opp4, @function
scalar_opp4:
.LFB4:
	.cfi_startproc
	endbr64
	xorl	%r8d, %r8d
	leaq	bal.2(%rip), %rcx
.L9:
	xorl	%eax, %eax
	.p2align 4,,10
	.p2align 3
.L10:
	movq	(%rcx,%rax), %rdx
	subq	(%rsi,%rax), %rdx
	movq	%rdx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	$40, %rax
	jne	.L10
	addl	$5, %r8d
	addq	$40, %rsi
	addq	$40, %rdi
	cmpl	$20, %r8d
	jne	.L9
	ret
	.cfi_endproc
.LFE4:
	.size	scalar_opp4, .-scalar_opp4
	.p2align 4
	.globl	scalar_carry4
	.type	scalar_carry4, @function
scalar_carry4:
.LFB5:
	.cfi_startproc
	endbr64
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	movq	%rsi, %rcx
	movq	(%rsi), %rsi
	movq	%rdi, %rdx
	movq	%rsi, %r8
	shrq	$51, %r8
	addq	8(%rcx), %r8
	movq	%r8, %r11
	shrq	$51, %r11
	addq	16(%rcx), %r11
	movq	%r11, %r10
	shrq	$51, %r10
	addq	24(%rcx), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	addq	32(%rcx), %r9
	movq	%r9, %rax
	shrq	$51, %rax
	leaq	(%rax,%rax,8), %rdi
	leaq	(%rax,%rdi,2), %rdi
	movabsq	$2251799813685247, %rax
	andq	%rax, %rsi
	andq	%rax, %r8
	andq	%rax, %r11
	andq	%rax, %r10
	addq	%rsi, %rdi
	andq	%rax, %r9
	movq	%r10, 24(%rdx)
	movq	%rdi, %rsi
	andq	%rax, %rdi
	movq	%r9, 32(%rdx)
	shrq	$51, %rsi
	movq	%rdi, (%rdx)
	addq	%r8, %rsi
	movq	%rsi, %rdi
	shrq	$51, %rsi
	addq	%r11, %rsi
	andq	%rax, %rdi
	movq	%rdi, 8(%rdx)
	movq	%rsi, 16(%rdx)
	movq	40(%rcx), %rsi
	movq	%rsi, %r8
	andq	%rax, %rsi
	shrq	$51, %r8
	addq	48(%rcx), %r8
	movq	%r8, %r11
	shrq	$51, %r11
	addq	56(%rcx), %r11
	movq	%r11, %r10
	shrq	$51, %r10
	addq	64(%rcx), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	addq	72(%rcx), %r9
	movq	%r9, %rdi
	shrq	$51, %rdi
	leaq	(%rdi,%rdi,8), %rbx
	leaq	(%rdi,%rbx,2), %rdi
	addq	%rsi, %rdi
	movq	%rdi, %rsi
	shrq	$51, %rsi
	andq	%rax, %r8
	andq	%rax, %rdi
	andq	%rax, %r11
	addq	%r8, %rsi
	movq	%rdi, 40(%rdx)
	andq	%rax, %r10
	andq	%rax, %r9
	movq	%rsi, %rdi
	shrq	$51, %rsi
	movq	%r10, 64(%rdx)
	addq	%r11, %rsi
	andq	%rax, %rdi
	movq	%r9, 72(%rdx)
	movq	%rdi, 48(%rdx)
	movq	%rsi, 56(%rdx)
	movq	80(%rcx), %rsi
	movq	%rsi, %r8
	andq	%rax, %rsi
	shrq	$51, %r8
	addq	88(%rcx), %r8
	movq	%r8, %r11
	andq	%rax, %r8
	shrq	$51, %r11
	addq	96(%rcx), %r11
	movq	%r11, %r10
	andq	%rax, %r11
	shrq	$51, %r10
	addq	104(%rcx), %r10
	movq	%r10, %r9
	andq	%rax, %r10
	shrq	$51, %r9
	addq	112(%rcx), %r9
	movq	%r10, 104(%rdx)
	movq	%r9, %rdi
	andq	%rax, %r9
	shrq	$51, %rdi
	movq	%r9, 112(%rdx)
	leaq	(%rdi,%rdi,8), %rbx
	leaq	(%rdi,%rbx,2), %rdi
	addq	%rsi, %rdi
	movq	%rdi, %rsi
	andq	%rax, %rdi
	shrq	$51, %rsi
	movq	%rdi, 80(%rdx)
	addq	%r8, %rsi
	movq	%rsi, %rdi
	shrq	$51, %rsi
	addq	%r11, %rsi
	andq	%rax, %rdi
	movq	%rdi, 88(%rdx)
	movq	%rsi, 96(%rdx)
	movq	120(%rcx), %r11
	popq	%rbx
	.cfi_def_cfa_offset 8
	movq	%r11, %r9
	shrq	$51, %r9
	addq	128(%rcx), %r9
	andq	%rax, %r11
	movq	%r9, %rdi
	andq	%rax, %r9
	shrq	$51, %rdi
	addq	136(%rcx), %rdi
	movq	%rdi, %r10
	andq	%rax, %rdi
	shrq	$51, %r10
	addq	144(%rcx), %r10
	movq	%r10, %rsi
	andq	%rax, %r10
	shrq	$51, %rsi
	addq	152(%rcx), %rsi
	movq	%r10, 144(%rdx)
	movq	%rsi, %rcx
	andq	%rax, %rsi
	shrq	$51, %rcx
	movq	%rsi, 152(%rdx)
	leaq	(%rcx,%rcx,8), %r8
	leaq	(%rcx,%r8,2), %r8
	addq	%r11, %r8
	movq	%r8, %rcx
	andq	%rax, %r8
	shrq	$51, %rcx
	movq	%r8, 120(%rdx)
	addq	%r9, %rcx
	movq	%rcx, %r8
	shrq	$51, %rcx
	andq	%rax, %r8
	addq	%rdi, %rcx
	movq	%r8, 128(%rdx)
	movq	%rcx, 136(%rdx)
	ret
	.cfi_endproc
.LFE5:
	.size	scalar_carry4, .-scalar_carry4
	.p2align 4
	.globl	scalar_carry_add4
	.type	scalar_carry_add4, @function
scalar_carry_add4:
.LFB6:
	.cfi_startproc
	endbr64
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	movq	%rsi, %rax
	movq	%rdi, %rcx
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	movq	(%rdx), %rbx
	movq	40(%rdx), %r11
	addq	(%rsi), %rbx
	addq	40(%rsi), %r11
	movq	48(%rdx), %r14
	movq	56(%rdx), %r13
	addq	48(%rsi), %r14
	addq	56(%rsi), %r13
	movq	64(%rdx), %r12
	movq	72(%rdx), %rbp
	addq	64(%rsi), %r12
	addq	72(%rsi), %rbp
	movq	80(%rdx), %r10
	movq	96(%rdx), %rdi
	addq	80(%rsi), %r10
	addq	96(%rax), %rdi
	movq	88(%rdx), %rsi
	addq	88(%rax), %rsi
	movq	%rdi, -24(%rsp)
	movq	%rsi, -32(%rsp)
	movq	104(%rdx), %r15
	movq	152(%rdx), %rdi
	addq	152(%rax), %rdi
	movq	136(%rdx), %rsi
	addq	136(%rax), %rsi
	movq	%rdi, -40(%rsp)
	movq	%rbx, %rdi
	movq	%rsi, -56(%rsp)
	shrq	$51, %rdi
	movq	8(%rdx), %rsi
	addq	8(%rax), %rsi
	movq	128(%rdx), %r8
	addq	%rdi, %rsi
	addq	128(%rax), %r8
	addq	104(%rax), %r15
	movq	%r8, -64(%rsp)
	movq	%rsi, %rdi
	movq	144(%rdx), %r8
	addq	144(%rax), %r8
	shrq	$51, %rdi
	movq	%r15, -16(%rsp)
	movq	%r8, -48(%rsp)
	movq	16(%rdx), %r8
	addq	16(%rax), %r8
	movq	112(%rdx), %r9
	addq	%rdi, %r8
	movq	24(%rdx), %rdi
	addq	24(%rax), %rdi
	movq	%r8, %r15
	addq	112(%rax), %r9
	shrq	$51, %r15
	movq	%r9, -8(%rsp)
	movq	120(%rdx), %r9
	addq	%r15, %rdi
	addq	120(%rax), %r9
	movq	32(%rdx), %rdx
	addq	32(%rax), %rdx
	movq	%rdi, %rax
	shrq	$51, %rax
	addq	%rax, %rdx
	movq	%rdx, %rax
	shrq	$51, %rax
	leaq	(%rax,%rax,8), %r15
	leaq	(%rax,%r15,2), %r15
	movabsq	$2251799813685247, %rax
	andq	%rax, %rbx
	addq	%r15, %rbx
	movq	%rbx, %r15
	shrq	$51, %r15
	andq	%rax, %rsi
	andq	%rax, %r8
	andq	%rax, %rbx
	addq	%r15, %rsi
	andq	%rax, %rdi
	andq	%rax, %rdx
	movq	%rbx, (%rcx)
	movq	%rsi, %r15
	shrq	$51, %rsi
	movq	%rdi, 24(%rcx)
	addq	%r8, %rsi
	andq	%rax, %r15
	movq	%r15, 8(%rcx)
	movq	%rsi, 16(%rcx)
	movq	%rdx, 32(%rcx)
	movq	%r11, %rdx
	andq	%rax, %r11
	movq	-16(%rsp), %r15
	shrq	$51, %rdx
	addq	%r14, %rdx
	movq	%rdx, %r14
	andq	%rax, %rdx
	shrq	$51, %r14
	movq	%r14, %r8
	addq	%r13, %r8
	movq	%r8, %r14
	andq	%rax, %r8
	shrq	$51, %r14
	movq	%r14, %rdi
	addq	%r12, %rdi
	movq	%rdi, %r14
	andq	%rax, %rdi
	shrq	$51, %r14
	movq	%rdi, 64(%rcx)
	movq	-24(%rsp), %rdi
	movq	%r14, %rsi
	addq	%rbp, %rsi
	movq	%rsi, %r14
	andq	%rax, %rsi
	shrq	$51, %r14
	movq	%rsi, 72(%rcx)
	movq	-32(%rsp), %rsi
	leaq	(%r14,%r14,8), %rbp
	leaq	(%r14,%rbp,2), %rbx
	addq	%rbx, %r11
	movq	-8(%rsp), %rbx
	movq	%r11, %r14
	andq	%rax, %r11
	shrq	$51, %r14
	movq	%r11, 40(%rcx)
	addq	%r14, %rdx
	movq	%rdx, %r11
	shrq	$51, %rdx
	andq	%rax, %r11
	addq	%r8, %rdx
	movq	%r11, 48(%rcx)
	movq	%r10, %r11
	shrq	$51, %r11
	movq	%rdx, 56(%rcx)
	addq	%rsi, %r11
	movq	%r11, %rdx
	shrq	$51, %rdx
	andq	%rax, %r10
	andq	%rax, %r11
	movq	%rdx, %r8
	addq	%rdi, %r8
	movq	%r8, %rdi
	andq	%rax, %r8
	shrq	$51, %rdi
	addq	%r15, %rdi
	movq	%rdi, %rdx
	andq	%rax, %rdi
	shrq	$51, %rdx
	movq	%rdi, 104(%rcx)
	movq	%rdx, %rsi
	addq	%rbx, %rsi
	movq	%rsi, %rdx
	andq	%rax, %rsi
	shrq	$51, %rdx
	movq	%rsi, 112(%rcx)
	movq	-56(%rsp), %rsi
	leaq	(%rdx,%rdx,8), %rbx
	leaq	(%rdx,%rbx,2), %rdx
	movq	-64(%rsp), %rbx
	addq	%rdx, %r10
	movq	%r10, %rdx
	andq	%rax, %r10
	shrq	$51, %rdx
	movq	%r10, 80(%rcx)
	addq	%r11, %rdx
	movq	%rdx, %r10
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %r10
	movq	%rdx, 96(%rcx)
	movq	%r9, %rdx
	andq	%rax, %r9
	shrq	$51, %rdx
	movq	%r10, 88(%rcx)
	movq	%rdx, %r8
	addq	%rbx, %r8
	movq	-48(%rsp), %rbx
	movq	%r8, %rdi
	andq	%rax, %r8
	shrq	$51, %rdi
	addq	%rsi, %rdi
	movq	%rdi, %r10
	shrq	$51, %r10
	addq	%rbx, %r10
	movq	-40(%rsp), %rbx
	movq	%r10, %rsi
	shrq	$51, %rsi
	addq	%rbx, %rsi
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	movq	%rsi, %rdx
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	shrq	$51, %rdx
	leaq	(%rdx,%rdx,8), %r11
	leaq	(%rdx,%r11,2), %rdx
	addq	%rdx, %r9
	movq	%r9, %rdx
	shrq	$51, %rdx
	addq	%r8, %rdx
	andq	%rax, %rdi
	andq	%rax, %r9
	andq	%rax, %r10
	movq	%rdx, %r8
	shrq	$51, %rdx
	andq	%rax, %rsi
	movq	%r9, 120(%rcx)
	andq	%rax, %r8
	addq	%rdi, %rdx
	movq	%r10, 144(%rcx)
	movq	%r8, 128(%rcx)
	movq	%rdx, 136(%rcx)
	movq	%rsi, 152(%rcx)
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE6:
	.size	scalar_carry_add4, .-scalar_carry_add4
	.p2align 4
	.globl	scalar_carry_sub4
	.type	scalar_carry_sub4, @function
scalar_carry_sub4:
.LFB7:
	.cfi_startproc
	endbr64
	subq	$184, %rsp
	.cfi_def_cfa_offset 192
	movq	%rdi, %r8
	xorl	%r10d, %r10d
	movq	%fs:40, %rax
	movq	%rax, 168(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rdi
	leaq	bal.1(%rip), %r9
.L18:
	xorl	%eax, %eax
	.p2align 4,,10
	.p2align 3
.L19:
	movq	(%rsi,%rax), %rcx
	addq	(%r9,%rax), %rcx
	subq	(%rdx,%rax), %rcx
	movq	%rcx, (%rdi,%rax)
	addq	$8, %rax
	cmpq	$40, %rax
	jne	.L19
	addl	$5, %r10d
	addq	$40, %rsi
	addq	$40, %rdx
	addq	$40, %rdi
	cmpl	$20, %r10d
	jne	.L18
	movq	(%rsp), %rdx
	movq	%rdx, %rsi
	shrq	$51, %rsi
	addq	8(%rsp), %rsi
	movq	%rsi, %r10
	shrq	$51, %r10
	addq	16(%rsp), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	addq	24(%rsp), %r9
	movq	%r9, %rdi
	shrq	$51, %rdi
	addq	32(%rsp), %rdi
	movq	%rdi, %rax
	shrq	$51, %rax
	leaq	(%rax,%rax,8), %rcx
	leaq	(%rax,%rcx,2), %rcx
	movabsq	$2251799813685247, %rax
	andq	%rax, %rdx
	andq	%rax, %rsi
	andq	%rax, %r10
	andq	%rax, %r9
	addq	%rdx, %rcx
	movq	%r9, 24(%r8)
	andq	%rax, %rdi
	movq	%rcx, %rdx
	andq	%rax, %rcx
	movq	%rdi, 32(%r8)
	shrq	$51, %rdx
	movq	%rcx, (%r8)
	addq	%rsi, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %rcx
	movq	%rdx, 16(%r8)
	movq	40(%rsp), %rdx
	movq	%rcx, 8(%r8)
	movq	%rdx, %rsi
	andq	%rax, %rdx
	shrq	$51, %rsi
	addq	48(%rsp), %rsi
	movq	%rsi, %r10
	shrq	$51, %r10
	addq	56(%rsp), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	addq	64(%rsp), %r9
	movq	%r9, %rdi
	shrq	$51, %rdi
	addq	72(%rsp), %rdi
	movq	%rdi, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rcx,8), %r11
	leaq	(%rcx,%r11,2), %rcx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	andq	%rax, %rsi
	andq	%rax, %rcx
	andq	%rax, %r10
	addq	%rsi, %rdx
	movq	%rcx, 40(%r8)
	andq	%rax, %r9
	andq	%rax, %rdi
	movq	%rdx, %rcx
	shrq	$51, %rdx
	movq	%r9, 64(%r8)
	addq	%r10, %rdx
	movq	%rdi, 72(%r8)
	andq	%rax, %rcx
	movq	%rdx, 56(%r8)
	movq	80(%rsp), %rdx
	movq	%rcx, 48(%r8)
	movq	%rdx, %rsi
	andq	%rax, %rdx
	shrq	$51, %rsi
	addq	88(%rsp), %rsi
	movq	%rsi, %r10
	andq	%rax, %rsi
	shrq	$51, %r10
	addq	96(%rsp), %r10
	movq	%r10, %r9
	andq	%rax, %r10
	shrq	$51, %r9
	addq	104(%rsp), %r9
	movq	%r9, %rdi
	andq	%rax, %r9
	shrq	$51, %rdi
	addq	112(%rsp), %rdi
	movq	%r9, 104(%r8)
	movq	%rdi, %rcx
	andq	%rax, %rdi
	shrq	$51, %rcx
	movq	%rdi, 112(%r8)
	leaq	(%rcx,%rcx,8), %r11
	leaq	(%rcx,%r11,2), %rcx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	andq	%rax, %rcx
	shrq	$51, %rdx
	movq	%rcx, 80(%r8)
	addq	%rsi, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %rcx
	movq	%rdx, 96(%r8)
	movq	120(%rsp), %rdx
	movq	%rcx, 88(%r8)
	movq	%rdx, %r10
	shrq	$51, %r10
	addq	128(%rsp), %r10
	andq	%rax, %rdx
	movq	%r10, %rdi
	andq	%rax, %r10
	shrq	$51, %rdi
	addq	136(%rsp), %rdi
	movq	%rdi, %rsi
	andq	%rax, %rdi
	shrq	$51, %rsi
	addq	144(%rsp), %rsi
	movq	%rsi, %rcx
	andq	%rax, %rsi
	shrq	$51, %rcx
	addq	152(%rsp), %rcx
	movq	%rsi, 144(%r8)
	movq	%rcx, %r9
	andq	%rax, %rcx
	shrq	$51, %r9
	movq	%rcx, 152(%r8)
	leaq	(%r9,%r9,8), %r11
	leaq	(%r9,%r11,2), %r9
	addq	%rdx, %r9
	movq	%r9, %rdx
	andq	%rax, %r9
	shrq	$51, %rdx
	movq	%r9, 120(%r8)
	addq	%r10, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r9
	addq	%rdi, %rdx
	movq	%r9, 128(%r8)
	movq	%rdx, 136(%r8)
	movq	168(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L24
	addq	$184, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L24:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE7:
	.size	scalar_carry_sub4, .-scalar_carry_sub4
	.p2align 4
	.globl	scalar_carry_opp4
	.type	scalar_carry_opp4, @function
scalar_carry_opp4:
.LFB8:
	.cfi_startproc
	endbr64
	subq	$184, %rsp
	.cfi_def_cfa_offset 192
	xorl	%r9d, %r9d
	leaq	bal.0(%rip), %r8
	movq	%fs:40, %rax
	movq	%rax, 168(%rsp)
	xorl	%eax, %eax
	movq	%rsp, %rcx
.L26:
	xorl	%eax, %eax
	.p2align 4,,10
	.p2align 3
.L27:
	movq	(%r8,%rax), %rdx
	subq	(%rsi,%rax), %rdx
	movq	%rdx, (%rcx,%rax)
	addq	$8, %rax
	cmpq	$40, %rax
	jne	.L27
	addl	$5, %r9d
	addq	$40, %rsi
	addq	$40, %rcx
	cmpl	$20, %r9d
	jne	.L26
	movq	(%rsp), %rdx
	movq	%rdx, %rsi
	shrq	$51, %rsi
	addq	8(%rsp), %rsi
	movq	%rsi, %r10
	shrq	$51, %r10
	addq	16(%rsp), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	addq	24(%rsp), %r9
	movq	%r9, %r8
	shrq	$51, %r8
	addq	32(%rsp), %r8
	movq	%r8, %rax
	shrq	$51, %rax
	leaq	(%rax,%rax,8), %rcx
	leaq	(%rax,%rcx,2), %rcx
	movabsq	$2251799813685247, %rax
	andq	%rax, %rdx
	andq	%rax, %rsi
	andq	%rax, %r10
	andq	%rax, %r9
	addq	%rdx, %rcx
	movq	%r9, 24(%rdi)
	andq	%rax, %r8
	movq	%rcx, %rdx
	andq	%rax, %rcx
	movq	%r8, 32(%rdi)
	shrq	$51, %rdx
	movq	%rcx, (%rdi)
	addq	%rsi, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %rcx
	movq	%rdx, 16(%rdi)
	movq	40(%rsp), %rdx
	movq	%rcx, 8(%rdi)
	movq	%rdx, %rsi
	andq	%rax, %rdx
	shrq	$51, %rsi
	addq	48(%rsp), %rsi
	movq	%rsi, %r10
	shrq	$51, %r10
	addq	56(%rsp), %r10
	movq	%r10, %r9
	shrq	$51, %r9
	addq	64(%rsp), %r9
	movq	%r9, %r8
	shrq	$51, %r8
	addq	72(%rsp), %r8
	movq	%r8, %rcx
	shrq	$51, %rcx
	leaq	(%rcx,%rcx,8), %r11
	leaq	(%rcx,%r11,2), %rcx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	shrq	$51, %rdx
	andq	%rax, %rsi
	andq	%rax, %rcx
	andq	%rax, %r10
	addq	%rsi, %rdx
	movq	%rcx, 40(%rdi)
	andq	%rax, %r9
	andq	%rax, %r8
	movq	%rdx, %rcx
	shrq	$51, %rdx
	movq	%r9, 64(%rdi)
	addq	%r10, %rdx
	movq	%r8, 72(%rdi)
	andq	%rax, %rcx
	movq	%rdx, 56(%rdi)
	movq	80(%rsp), %rdx
	movq	%rcx, 48(%rdi)
	movq	%rdx, %rsi
	andq	%rax, %rdx
	shrq	$51, %rsi
	addq	88(%rsp), %rsi
	movq	%rsi, %r10
	andq	%rax, %rsi
	shrq	$51, %r10
	addq	96(%rsp), %r10
	movq	%r10, %r9
	andq	%rax, %r10
	shrq	$51, %r9
	addq	104(%rsp), %r9
	movq	%r9, %r8
	andq	%rax, %r9
	shrq	$51, %r8
	addq	112(%rsp), %r8
	movq	%r9, 104(%rdi)
	movq	%r8, %rcx
	andq	%rax, %r8
	shrq	$51, %rcx
	movq	%r8, 112(%rdi)
	leaq	(%rcx,%rcx,8), %r11
	leaq	(%rcx,%r11,2), %rcx
	addq	%rdx, %rcx
	movq	%rcx, %rdx
	andq	%rax, %rcx
	shrq	$51, %rdx
	movq	%rcx, 80(%rdi)
	addq	%rsi, %rdx
	movq	%rdx, %rcx
	shrq	$51, %rdx
	addq	%r10, %rdx
	andq	%rax, %rcx
	movq	%rdx, 96(%rdi)
	movq	120(%rsp), %rdx
	movq	%rcx, 88(%rdi)
	movq	%rdx, %r10
	shrq	$51, %r10
	addq	128(%rsp), %r10
	andq	%rax, %rdx
	movq	%r10, %r8
	andq	%rax, %r10
	shrq	$51, %r8
	addq	136(%rsp), %r8
	movq	%r8, %rsi
	andq	%rax, %r8
	shrq	$51, %rsi
	addq	144(%rsp), %rsi
	movq	%rsi, %rcx
	andq	%rax, %rsi
	shrq	$51, %rcx
	addq	152(%rsp), %rcx
	movq	%rsi, 144(%rdi)
	movq	%rcx, %r9
	andq	%rax, %rcx
	shrq	$51, %r9
	movq	%rcx, 152(%rdi)
	leaq	(%r9,%r9,8), %r11
	leaq	(%r9,%r11,2), %r9
	addq	%rdx, %r9
	movq	%r9, %rdx
	andq	%rax, %r9
	shrq	$51, %rdx
	movq	%r9, 120(%rdi)
	addq	%r10, %rdx
	movq	%rdx, %r9
	shrq	$51, %rdx
	andq	%rax, %r9
	addq	%r8, %rdx
	movq	%r9, 128(%rdi)
	movq	%rdx, 136(%rdi)
	movq	168(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L32
	addq	$184, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L32:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE8:
	.size	scalar_carry_opp4, .-scalar_carry_opp4
	.section	.rodata
	.align 32
	.type	bal.3, @object
	.size	bal.3, 40
bal.3:
	.quad	4503599627370458
	.quad	4503599627370494
	.quad	4503599627370494
	.quad	4503599627370494
	.quad	4503599627370494
	.set	bal.0,bal.3
	.set	bal.1,bal.3
	.set	bal.2,bal.3
	.ident	"GCC: (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
