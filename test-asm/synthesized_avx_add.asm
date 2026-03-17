SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	vmovdqu ymm0, [rsi]
	vpaddq ymm0, ymm0, [rdx]
	vmovdqu [rdi], ymm0
	vmovdqu ymm1, [rsi + 0x08 * 4]
	vpaddq ymm1, ymm1, [rdx + 0x08 * 4]
	vmovdqu [rdi + 0x08 * 4], ymm1
	vmovdqu ymm2, [rsi + 0x08 * 8]
	vpaddq ymm2, ymm2, [rdx + 0x08 * 8]
	vmovdqu [rdi + 0x08 * 8], ymm2
	vmovdqu ymm3, [rsi + 0x08 * 12]
	vpaddq ymm3, ymm3, [rdx + 0x08 * 12]
	vmovdqu [rdi + 0x08 * 12], ymm3
	vmovdqu ymm4, [rsi + 0x08 * 16]
	vpaddq ymm4, ymm4, [rdx + 0x08 * 16]
	vmovdqu [rdi + 0x08 * 16], ymm4
	vzeroupper
	ret
