	.macosx_version_min 10, 13
	.section	__TEXT,__text,regular,pure_instructions
	.section	__TEXT,__const
	.p2align	5, 0x0                          ## -- Begin function simple_crypto_step___un_3C_uni_3E_un_3C_uni_3E_uni
LCPI0_0:
	.long	0                               ## 0x0
	.long	4                               ## 0x4
	.long	8                               ## 0x8
	.long	12                              ## 0xc
	.long	0                               ## 0x0
	.long	4                               ## 0x4
	.long	8                               ## 0x8
	.long	12                              ## 0xc
LCPI0_1:
	.long	0                               ## 0x0
	.long	1                               ## 0x1
	.long	2                               ## 0x2
	.long	3                               ## 0x3
	.long	4                               ## 0x4
	.long	5                               ## 0x5
	.long	6                               ## 0x6
	.long	7                               ## 0x7
	.section	__TEXT,__literal16,16byte_literals
	.p2align	4, 0x0
LCPI0_2:
	.long	0                               ## 0x0
	.long	4                               ## 0x4
	.long	8                               ## 0x8
	.long	12                              ## 0xc
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_simple_crypto_step___un_3C_uni_3E_un_3C_uni_3E_uni
	.p2align	4
_simple_crypto_step___un_3C_uni_3E_un_3C_uni_3E_uni: ## @simple_crypto_step___un_3C_uni_3E_un_3C_uni_3E_uni
## %bb.0:
                                        ## kill: def $edx killed $edx def $rdx
	leal	7(%rdx), %eax
	testl	%edx, %edx
	cmovnsl	%edx, %eax
	andl	$-8, %eax
	jle	LBB0_1
## %bb.2:
	vpcmpeqd	%ymm1, %ymm1, %ymm1
	vbroadcasti128	LCPI0_2(%rip), %ymm2    ## ymm2 = [0,4,8,12,0,4,8,12]
                                        ## ymm2 = mem[0,1,0,1]
	vpxor	%xmm0, %xmm0, %xmm0
	vpgatherdd	%ymm1, (%rsi,%ymm2), %ymm0
	movl	%eax, %ecx
	xorl	%eax, %eax
	.p2align	4
LBB0_3:                                 ## =>This Inner Loop Header: Depth=1
	vpaddd	(%rdi,%rax,4), %ymm0, %ymm1
	vmovdqu	%ymm1, (%rdi,%rax,4)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jb	LBB0_3
## %bb.4:
	cmpl	%edx, %eax
	jge	LBB0_6
LBB0_5:
	vmovd	%eax, %xmm0
	vpbroadcastd	%xmm0, %ymm0
	vpor	LCPI0_1(%rip), %ymm0, %ymm0
	vmovd	%edx, %xmm1
	vpbroadcastd	%xmm1, %ymm1
	vpcmpgtd	%ymm0, %ymm1, %ymm0
	shll	$2, %eax
	vbroadcasti128	LCPI0_2(%rip), %ymm1    ## ymm1 = [0,4,8,12,0,4,8,12]
                                        ## ymm1 = mem[0,1,0,1]
	vpxor	%xmm2, %xmm2, %xmm2
	vmovdqa	%ymm0, %ymm3
	vpgatherdd	%ymm3, (%rsi,%ymm1), %ymm2
	vmaskmovps	(%rdi,%rax), %ymm0, %ymm1
	vpaddd	%ymm1, %ymm2, %ymm1
	vmaskmovps	%ymm1, %ymm0, (%rdi,%rax)
LBB0_6:
	vzeroupper
	retq
LBB0_1:
	xorl	%eax, %eax
	cmpl	%edx, %eax
	jl	LBB0_5
	jmp	LBB0_6
                                        ## -- End function
	.section	__TEXT,__const
	.p2align	5, 0x0                          ## -- Begin function simple_crypto_step
LCPI1_0:
	.long	0                               ## 0x0
	.long	4                               ## 0x4
	.long	8                               ## 0x8
	.long	12                              ## 0xc
	.long	0                               ## 0x0
	.long	4                               ## 0x4
	.long	8                               ## 0x8
	.long	12                              ## 0xc
LCPI1_1:
	.long	0                               ## 0x0
	.long	1                               ## 0x1
	.long	2                               ## 0x2
	.long	3                               ## 0x3
	.long	4                               ## 0x4
	.long	5                               ## 0x5
	.long	6                               ## 0x6
	.long	7                               ## 0x7
	.section	__TEXT,__literal16,16byte_literals
	.p2align	4, 0x0
LCPI1_2:
	.long	0                               ## 0x0
	.long	4                               ## 0x4
	.long	8                               ## 0x8
	.long	12                              ## 0xc
	.section	__TEXT,__text,regular,pure_instructions
	.globl	_simple_crypto_step
	.p2align	4
_simple_crypto_step:                    ## @simple_crypto_step
## %bb.0:
                                        ## kill: def $edx killed $edx def $rdx
	leal	7(%rdx), %eax
	testl	%edx, %edx
	cmovnsl	%edx, %eax
	andl	$-8, %eax
	jle	LBB1_1
## %bb.2:
	vpcmpeqd	%ymm1, %ymm1, %ymm1
	vbroadcasti128	LCPI1_2(%rip), %ymm2    ## ymm2 = [0,4,8,12,0,4,8,12]
                                        ## ymm2 = mem[0,1,0,1]
	vpxor	%xmm0, %xmm0, %xmm0
	vpgatherdd	%ymm1, (%rsi,%ymm2), %ymm0
	movl	%eax, %ecx
	xorl	%eax, %eax
	.p2align	4
LBB1_3:                                 ## =>This Inner Loop Header: Depth=1
	vpaddd	(%rdi,%rax,4), %ymm0, %ymm1
	vmovdqu	%ymm1, (%rdi,%rax,4)
	addq	$8, %rax
	cmpq	%rcx, %rax
	jb	LBB1_3
## %bb.4:
	cmpl	%edx, %eax
	jge	LBB1_6
LBB1_5:
	vmovd	%eax, %xmm0
	vpbroadcastd	%xmm0, %ymm0
	vpor	LCPI1_1(%rip), %ymm0, %ymm0
	vmovd	%edx, %xmm1
	vpbroadcastd	%xmm1, %ymm1
	vpcmpgtd	%ymm0, %ymm1, %ymm0
	shll	$2, %eax
	vbroadcasti128	LCPI1_2(%rip), %ymm1    ## ymm1 = [0,4,8,12,0,4,8,12]
                                        ## ymm1 = mem[0,1,0,1]
	vpxor	%xmm2, %xmm2, %xmm2
	vmovdqa	%ymm0, %ymm3
	vpgatherdd	%ymm3, (%rsi,%ymm1), %ymm2
	vmaskmovps	(%rdi,%rax), %ymm0, %ymm1
	vpaddd	%ymm1, %ymm2, %ymm1
	vmaskmovps	%ymm1, %ymm0, (%rdi,%rax)
LBB1_6:
	vzeroupper
	retq
LBB1_1:
	xorl	%eax, %eax
	cmpl	%edx, %eax
	jl	LBB1_5
	jmp	LBB1_6
                                        ## -- End function
.subsections_via_symbols
