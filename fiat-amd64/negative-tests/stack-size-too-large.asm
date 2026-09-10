SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
; This is a deliberately hostile hints file (scrutineer finding #2517):
; the single instruction below makes the inferred stack size 4 GiB.  The
; equivalence checker must reject it immediately with a "Stack size ...
; exceeds the maximum supported stack size" error rather than attempting
; to model that many stack cells (which would exhaust memory).
sub rsp, 0x100000000
ret
