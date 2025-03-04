_Z24fiat_25519_addcarryx_u51PmPhhmm:
        movabs  rax, 2251799813685247
        add     rcx, r8
        movzx   edx, dl
        add     rcx, rdx
        and     rax, rcx
        shr     rcx, 51
        mov     QWORD PTR [rdi], rax
        mov     BYTE PTR [rsi], cl
        ret
_Z25fiat_25519_subborrowx_u51PmPhhmm:
        movabs  rax, 2251799813685247
        movzx   edx, dl
        sub     rcx, rdx
        sub     rcx, r8
        and     rax, rcx
        sar     rcx, 51
        neg     ecx
        mov     QWORD PTR [rdi], rax
        mov     BYTE PTR [rsi], cl
        ret
_Z22fiat_25519_cmovznz_u64Pmhmm:
        cmp     sil, 1
        sbb     rax, rax
        and     rax, rdx
        xor     edx, edx
        test    sil, sil
        cmove   rcx, rdx
        or      rax, rcx
        mov     QWORD PTR [rdi], rax
        ret
_Z20fiat_25519_carry_mulPmPKmS1_:
        push    r15
        mov     rcx, rsi
        mov     rax, rdx
        push    r14
        push    r13
        push    r12
        xor     r12d, r12d
        push    rbp
        mov     rbp, rdi
        push    rbx
        sub     rsp, 16
        mov     r11, QWORD PTR [rcx+24]
        mov     r15, QWORD PTR [rdx+32]
        mov     rbx, QWORD PTR [rsi+32]
        mov     r14, QWORD PTR [rax+24]
        xor     esi, esi
        mov     QWORD PTR [rsp-48], r12
        mov     QWORD PTR [rsp-56], r11
        mov     r11, QWORD PTR [rcx+16]
        lea     rdx, [r15+r15*8]
        xor     r12d, r12d
        mov     QWORD PTR [rsp-104], rbx
        mov     rbx, QWORD PTR [rax+16]
        lea     rdi, [r15+rdx*2]
        lea     rdx, [r14+r14*8]
        mov     r10, QWORD PTR [rax]
        mov     QWORD PTR [rsp-96], rsi
        lea     r8, [r14+rdx*2]
        mov     rsi, QWORD PTR [rax+8]
        mov     rax, QWORD PTR [rcx]
        mov     QWORD PTR [rsp-72], r11
        lea     rdx, [rbx+rbx*8]
        mov     r11, QWORD PTR [rcx+8]
        mov     QWORD PTR [rsp-64], r12
        xor     r12d, r12d
        lea     r9, [rbx+rdx*2]
        mov     QWORD PTR [rsp-80], r12
        xor     edx, edx
        mov     QWORD PTR [rsp-88], r11
        xor     r11d, r11d
        mov     QWORD PTR [rsp-8], rax
        lea     rax, [rsi+rsi*8]
        mov     QWORD PTR [rsp], rdx
        lea     rax, [rsi+rax*2]
        mul     QWORD PTR [rcx+32]
        mov     QWORD PTR [rsp-120], r10
        mov     QWORD PTR [rsp-112], r11
        mov     r12, rax
        mov     r13, rdx
        mov     rax, r9
        mul     QWORD PTR [rcx+24]
        add     r12, rax
        mov     rax, r8
        adc     r13, rdx
        mul     QWORD PTR [rcx+16]
        add     r12, rax
        mov     rax, rdi
        adc     r13, rdx
        mul     QWORD PTR [rcx+8]
        add     r12, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r13, rdx
        mul     QWORD PTR [rcx]
        add     r12, rax
        mov     rax, QWORD PTR [rsp-104]
        adc     r13, rdx
        mov     QWORD PTR [rsp-40], r12
        mul     r9
        mov     QWORD PTR [rsp-32], r13
        mov     r10, rax
        mov     r11, rdx
        mov     rax, r8
        mul     QWORD PTR [rcx+24]
        add     r10, rax
        mov     rax, rdi
        adc     r11, rdx
        mul     QWORD PTR [rcx+16]
        mov     r9, r10
        mov     r10, r11
        mov     r11, QWORD PTR [rsp-32]
        add     r9, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r10, rdx
        mul     QWORD PTR [rsp-88]
        mov     r12, r9
        mov     r13, r10
        mov     r10, QWORD PTR [rsp-40]
        add     r12, rax
        mov     rax, rsi
        adc     r13, rdx
        mul     QWORD PTR [rcx]
        add     rax, r12
        adc     rdx, r13
        shrd    r10, r11, 51
        xor     r11d, r11d
        add     rax, r10
        mov     r12, rax
        mov     rax, QWORD PTR [rsp-104]
        adc     rdx, r11
        mov     r13, rdx
        mov     QWORD PTR [rsp-24], r12
        mul     r8
        mov     QWORD PTR [rsp-16], r13
        mov     r8, rax
        mov     r9, rdx
        mov     rax, rdi
        mul     QWORD PTR [rcx+24]
        add     r8, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r9, rdx
        mul     QWORD PTR [rsp-72]
        add     r8, rax
        mov     rax, QWORD PTR [rsp-88]
        adc     r9, rdx
        mov     r10, r8
        mov     r8, r12
        mul     rsi
        mov     r11, r9
        add     r10, rax
        mov     rax, rbx
        adc     r11, rdx
        mul     QWORD PTR [rcx]
        add     rax, r10
        adc     rdx, r11
        shrd    r8, r13, 51
        xor     r9d, r9d
        add     rax, r8
        mov     r12, rax
        mov     rax, QWORD PTR [rsp-104]
        adc     rdx, r9
        mov     r13, rdx
        mul     rdi
        mov     r10, rax
        mov     r11, rdx
        mov     rax, QWORD PTR [rsp-120]
        mul     QWORD PTR [rsp-56]
        add     r10, rax
        mov     rax, QWORD PTR [rsp-72]
        adc     r11, rdx
        mul     rsi
        add     r10, rax
        mov     rax, QWORD PTR [rsp-88]
        adc     r11, rdx
        mul     rbx
        add     r10, rax
        mov     rax, r14
        adc     r11, rdx
        mul     QWORD PTR [rcx]
        mov     r8, rax
        mov     r9, rdx
        mov     rax, r12
        add     r8, r10
        adc     r9, r11
        shrd    rax, r13, 51
        xor     r11d, r11d
        add     r8, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r9, r11
        mul     QWORD PTR [rsp-104]
        mov     r10, rax
        mov     rax, QWORD PTR [rsp-56]
        mov     r11, rdx
        mul     rsi
        add     r10, rax
        mov     rax, QWORD PTR [rsp-72]
        adc     r11, rdx
        mov     rcx, r10
        mul     rbx
        mov     rbx, r11
        add     rcx, rax
        mov     rax, QWORD PTR [rsp-88]
        adc     rbx, rdx
        mul     r14
        add     rcx, rax
        mov     rax, QWORD PTR [rsp-8]
        adc     rbx, rdx
        mul     r15
        add     rax, rcx
        mov     rcx, r8
        adc     rdx, rbx
        shrd    rcx, r9, 51
        xor     ebx, ebx
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, rax
        shrd    rcx, rdx, 51
        lea     rdx, [rcx+rcx*8]
        lea     rsi, [rcx+rdx*2]
        mov     rdx, QWORD PTR [rsp-40]
        movabs  rcx, 2251799813685247
        and     r12, rcx
        and     r8, rcx
        and     rax, rcx
        and     rdx, rcx
        mov     QWORD PTR [rbp+24], r8
        add     rsi, rdx
        mov     rdx, QWORD PTR [rsp-24]
        mov     QWORD PTR [rbp+32], rax
        mov     rdi, rsi
        and     rsi, rcx
        and     rdx, rcx
        shr     rdi, 51
        mov     QWORD PTR [rbp+0], rsi
        add     rdx, rdi
        mov     rsi, rdx
        shr     rdx, 51
        add     rdx, r12
        and     rsi, rcx
        mov     QWORD PTR [rbp+8], rsi
        mov     QWORD PTR [rbp+16], rdx
        add     rsp, 16
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
_Z23fiat_25519_carry_squarePmPKm:
        push    r15
        xor     edx, edx
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        mov     r12, QWORD PTR [rsi+32]
        mov     rbx, rdi
        mov     r8, QWORD PTR [rsi+24]
        mov     rcx, QWORD PTR [rsi+8]
        lea     rax, [r12+r12*8]
        mov     rbp, QWORD PTR [rsi+16]
        lea     r13, [r12+rax*2]
        lea     rax, [r8+r8]
        mov     QWORD PTR [rsp-48], rdx
        mov     QWORD PTR [rsp-24], rax
        mov     rax, QWORD PTR [rsi]
        lea     r9, [r13+r13]
        lea     rdi, [rbp+rbp]
        mov     QWORD PTR [rsp-16], rdi
        mov     QWORD PTR [rsp-56], rax
        lea     rax, [r8+r8*8]
        lea     rsi, [r8+rax*2]
        lea     r14, [rsi+rsi]
        mov     rax, r14
        mov     r14, QWORD PTR [rsp-56]
        mul     rbp
        mov     r10, rax
        mov     rax, r9
        mov     r11, rdx
        mul     rcx
        add     r10, rax
        mov     rax, r14
        adc     r11, rdx
        mul     QWORD PTR [rsp-56]
        mov     r14, r10
        mov     r15, r11
        add     r14, rax
        mov     rax, rsi
        lea     rsi, [rcx+rcx]
        adc     r15, rdx
        mul     r8
        mov     QWORD PTR [rsp-40], r14
        mov     QWORD PTR [rsp-32], r15
        mov     r10, rax
        mov     rax, r9
        mov     r11, rdx
        mul     rbp
        add     r10, rax
        mov     rax, rsi
        adc     r11, rdx
        mul     QWORD PTR [rsp-56]
        mov     rsi, rax
        mov     rdi, rdx
        mov     rax, r9
        add     rsi, r10
        mov     r10, r14
        adc     rdi, r11
        shrd    r10, r15, 51
        xor     edx, edx
        add     rsi, r10
        adc     rdi, rdx
        mul     r8
        mov     r8, rax
        mov     r9, rdx
        mov     rax, QWORD PTR [rsp-16]
        mul     QWORD PTR [rsp-56]
        mov     r10, rax
        mov     r11, rdx
        mov     rax, rcx
        add     r10, r8
        mov     r8, rsi
        adc     r11, r9
        mul     rcx
        add     r10, rax
        mov     rax, r13
        adc     r11, rdx
        shrd    r8, rdi, 51
        xor     edx, edx
        add     r10, r8
        adc     r11, rdx
        mul     r12
        mov     r13, r10
        mov     r14, rax
        mov     rax, QWORD PTR [rsp-16]
        mov     r15, rdx
        mul     rcx
        mov     r8, rax
        mov     r9, rdx
        mov     rax, QWORD PTR [rsp-24]
        add     r8, r14
        adc     r9, r15
        mul     QWORD PTR [rsp-56]
        add     r8, rax
        adc     r9, rdx
        shrd    r13, r11, 51
        xor     edx, edx
        add     r8, r13
        adc     r9, rdx
        add     r12, r12
        mov     rax, r12
        mul     QWORD PTR [rsp-56]
        mov     r12, rax
        mov     rax, QWORD PTR [rsp-24]
        mov     r13, rdx
        mul     rcx
        add     r12, rax
        mov     rax, rbp
        adc     r13, rdx
        mul     rbp
        movabs  rbp, 2251799813685247
        add     rax, r12
        mov     r12, r8
        adc     rdx, r13
        shrd    r12, r9, 51
        xor     r13d, r13d
        add     rax, r12
        adc     rdx, r13
        mov     rcx, rax
        and     rsi, rbp
        and     r10, rbp
        shrd    rcx, rdx, 51
        and     r8, rbp
        and     rax, rbp
        lea     rdx, [rcx+rcx*8]
        mov     QWORD PTR [rbx+24], r8
        lea     rdx, [rcx+rdx*2]
        mov     rcx, QWORD PTR [rsp-40]
        mov     QWORD PTR [rbx+32], rax
        and     rcx, rbp
        add     rdx, rcx
        mov     rcx, rdx
        and     rdx, rbp
        shr     rcx, 51
        mov     QWORD PTR [rbx], rdx
        add     rsi, rcx
        mov     rdx, rsi
        shr     rsi, 51
        and     rdx, rbp
        add     rsi, r10
        mov     QWORD PTR [rbx+8], rdx
        mov     QWORD PTR [rbx+16], rsi
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
_Z29fiat_25519_carry_scmul_121666PmPKm:
        push    r15
        mov     r11d, 121666
        mov     r10, rsi
        mov     rcx, rdi
        push    r14
        push    r13
        push    r12
        mov     r14, QWORD PTR [rsi]
        mov     rax, r14
        mul     r11
        mov     r14, rax
        mov     rax, QWORD PTR [rsi+8]
        mov     r15, rdx
        mov     r8, r14
        mov     r9, r15
        mul     r11
        shrd    r8, r15, 51
        shr     r9, 51
        add     r8, rax
        mov     rax, QWORD PTR [rsi+16]
        adc     r9, rdx
        mov     rsi, r8
        mul     r11
        mov     rdi, r9
        shrd    rsi, r9, 51
        shr     rdi, 51
        add     rsi, rax
        mov     rax, QWORD PTR [r10+24]
        adc     rdi, rdx
        mov     QWORD PTR [rsp-24], rsi
        mul     r11
        shrd    rsi, rdi, 51
        mov     QWORD PTR [rsp-16], rdi
        shr     rdi, 51
        mov     r12, rsi
        mov     r13, rdi
        mov     rsi, QWORD PTR [rsp-24]
        add     r12, rax
        mov     rax, QWORD PTR [r10+32]
        adc     r13, rdx
        mov     r10, r12
        mul     r11
        shrd    r10, r13, 51
        mov     r11, r13
        shr     r11, 51
        add     r10, rax
        adc     r11, rdx
        mov     rdi, r10
        mov     rax, r10
        shrd    rdi, r11, 51
        lea     rdx, [rdi+rdi*8]
        lea     rdx, [rdi+rdx*2]
        movabs  rdi, 2251799813685247
        and     r14, rdi
        and     r8, rdi
        and     rsi, rdi
        and     r12, rdi
        add     r14, rdx
        and     rax, rdi
        mov     QWORD PTR [rcx+24], r12
        pop     r12
        mov     rdx, r14
        and     r14, rdi
        pop     r13
        mov     QWORD PTR [rcx+32], rax
        shr     rdx, 51
        mov     QWORD PTR [rcx], r14
        pop     r14
        add     r8, rdx
        pop     r15
        mov     rdx, r8
        shr     r8, 51
        and     rdx, rdi
        add     r8, rsi
        mov     QWORD PTR [rcx+8], rdx
        mov     QWORD PTR [rcx+16], r8
        ret
_Z16fiat_25519_carryPmPKm:
        mov     rax, QWORD PTR [rsi]
        mov     rdx, rdi
        mov     r9, rax
        shr     r9, 51
        add     r9, QWORD PTR [rsi+8]
        mov     rdi, r9
        shr     rdi, 51
        add     rdi, QWORD PTR [rsi+16]
        mov     r10, rdi
        shr     r10, 51
        add     r10, QWORD PTR [rsi+24]
        mov     rcx, r10
        shr     rcx, 51
        add     rcx, QWORD PTR [rsi+32]
        mov     rsi, rcx
        shr     rcx, 51
        lea     r8, [rcx+rcx*8]
        lea     r8, [rcx+r8*2]
        movabs  rcx, 2251799813685247
        and     rax, rcx
        and     r9, rcx
        and     rdi, rcx
        and     r10, rcx
        add     r8, rax
        and     rsi, rcx
        mov     QWORD PTR [rdx+24], r10
        mov     rax, r8
        and     r8, rcx
        mov     QWORD PTR [rdx+32], rsi
        shr     rax, 51
        mov     QWORD PTR [rdx], r8
        add     rax, r9
        mov     r8, rax
        shr     rax, 51
        and     r8, rcx
        add     rax, rdi
        mov     QWORD PTR [rdx+8], r8
        mov     QWORD PTR [rdx+16], rax
        ret
_Z14fiat_25519_addPmPKmS1_:
        movdqu  xmm0, XMMWORD PTR [rsi+16]
        movdqu  xmm3, XMMWORD PTR [rdx+16]
        movdqu  xmm1, XMMWORD PTR [rsi]
        movdqu  xmm2, XMMWORD PTR [rdx]
        mov     rax, QWORD PTR [rdx+32]
        paddq   xmm0, xmm3
        add     rax, QWORD PTR [rsi+32]
        paddq   xmm1, xmm2
        mov     QWORD PTR [rdi+32], rax
        movups  XMMWORD PTR [rdi], xmm1
        movups  XMMWORD PTR [rdi+16], xmm0
        ret
_Z14fiat_25519_subPmPKmS1_:
        movdqu  xmm0, XMMWORD PTR [rsi+16]
        movdqu  xmm3, XMMWORD PTR [rdx+16]
        movabs  rax, 4503599627370494
        movq    xmm1, rax
        movdqu  xmm2, XMMWORD PTR [rdx]
        add     rax, QWORD PTR [rsi+32]
        punpcklqdq      xmm1, xmm1
        psubq   xmm0, xmm3
        sub     rax, QWORD PTR [rdx+32]
        paddq   xmm0, xmm1
        movdqu  xmm1, XMMWORD PTR [rsi]
        mov     QWORD PTR [rdi+32], rax
        movups  XMMWORD PTR [rdi+16], xmm0
        psubq   xmm1, xmm2
        paddq   xmm1, XMMWORD PTR .LC1[rip]
        movups  XMMWORD PTR [rdi], xmm1
        ret
_Z14fiat_25519_oppPmPKm:
        movabs  rax, 4503599627370494
        movdqu  xmm3, XMMWORD PTR [rsi+16]
        movdqu  xmm2, XMMWORD PTR [rsi]
        movq    xmm0, rax
        movdqa  xmm1, XMMWORD PTR .LC1[rip]
        sub     rax, QWORD PTR [rsi+32]
        punpcklqdq      xmm0, xmm0
        mov     QWORD PTR [rdi+32], rax
        psubq   xmm0, xmm3
        psubq   xmm1, xmm2
        movups  XMMWORD PTR [rdi], xmm1
        movups  XMMWORD PTR [rdi+16], xmm0
        ret
_Z20fiat_25519_selectznzPmhPKmS1_:
        mov     r8, rdx
        cmp     sil, 1
        push    rbp
        sbb     rdx, rdx
        mov     r9, QWORD PTR [r8+8]
        xor     eax, eax
        push    rbx
        test    sil, sil
        mov     rbx, rax
        cmovne  rbx, QWORD PTR [rcx+8]
        mov     r11, rax
        and     r9, rdx
        mov     r10, rax
        mov     rbp, QWORD PTR [r8+32]
        or      rbx, r9
        mov     r9, QWORD PTR [r8+16]
        test    sil, sil
        cmovne  r11, QWORD PTR [rcx+16]
        and     r9, rdx
        or      r11, r9
        mov     r9, QWORD PTR [r8+24]
        test    sil, sil
        cmovne  r10, QWORD PTR [rcx+24]
        and     r9, rdx
        or      r10, r9
        test    sil, sil
        mov     r9, rax
        cmovne  r9, QWORD PTR [rcx+32]
        and     rbp, rdx
        or      r9, rbp
        test    sil, sil
        cmovne  rax, QWORD PTR [rcx]
        and     rdx, QWORD PTR [r8]
        mov     QWORD PTR [rdi+8], rbx
        pop     rbx
        or      rax, rdx
        mov     QWORD PTR [rdi+16], r11
        pop     rbp
        mov     QWORD PTR [rdi], rax
        mov     QWORD PTR [rdi+24], r10
        mov     QWORD PTR [rdi+32], r9
        ret
_Z19fiat_25519_to_bytesPhPKm:
        movabs  rdx, -2251799813685247
        push    rbp
        xor     r9d, r9d
        push    rbx
        mov     rcx, QWORD PTR [rsi+8]
        movabs  rbx, -2251799813685229
        add     rbx, QWORD PTR [rsi]
        mov     r11, QWORD PTR [rsi+24]
        mov     rax, rbx
        sar     rax, 51
        add     r11, rdx
        neg     eax
        movzx   eax, al
        sub     rcx, rax
        mov     rax, QWORD PTR [rsi+16]
        add     rcx, rdx
        mov     r8, rcx
        add     rax, rdx
        add     rdx, QWORD PTR [rsi+32]
        sar     r8, 51
        neg     r8d
        movzx   r8d, r8b
        sub     rax, r8
        movabs  r8, 2251799813685247
        mov     r10, rax
        sar     rax, 51
        neg     eax
        movzx   eax, al
        sub     r11, rax
        mov     rax, r11
        sar     rax, 51
        neg     eax
        movzx   eax, al
        sub     rdx, rax
        movabs  rax, 2251799813685229
        mov     rbp, rdx
        sar     rbp, 51
        test    bpl, bpl
        cmove   rax, r9
        and     rbx, r8
        add     rax, rbx
        movabs  rbx, 144115188075855808
        mov     rsi, rax
        and     rsi, r8
        test    bpl, bpl
        cmovne  r9, r8
        and     rcx, r8
        shr     rax, 51
        and     r11, r8
        and     rdx, r8
        mov     DWORD PTR [rdi], esi
        add     rcx, r9
        add     r11, r9
        add     rdx, r9
        add     rcx, rax
        mov     rax, r10
        and     rax, r8
        mov     r10, rcx
        sal     rcx, 3
        shr     r10, 51
        add     rax, r9
        add     rax, r10
        mov     r10, rax
        sal     rax, 6
        shr     r10, 51
        and     rax, rbx
        add     r11, r10
        movabs  r10, 18014398509481976
        and     rcx, r10
        mov     r10, rsi
        mov     rbx, r11
        shr     r11, 51
        shr     r10, 48
        and     rbx, r8
        add     rdx, r11
        movabs  r8, 36028797018963952
        add     r10, rcx
        shr     rcx, 48
        add     rax, rcx
        sal     rdx, 4
        mov     DWORD PTR [rdi+6], r10d
        mov     rcx, rax
        and     rdx, r8
        mov     DWORD PTR [rdi+12], eax
        shr     rcx, 56
        lea     rcx, [rcx+rbx*2]
        pop     rbx
        pop     rbp
        mov     r8, rcx
        mov     DWORD PTR [rdi+19], ecx
        shr     r8, 48
        add     rdx, r8
        mov     r8, rsi
        shr     rsi, 40
        mov     BYTE PTR [rdi+5], sil
        mov     rsi, r10
        shr     r8, 32
        shr     rsi, 32
        mov     DWORD PTR [rdi+25], edx
        shr     r10, 40
        mov     BYTE PTR [rdi+10], sil
        mov     rsi, rax
        shr     rsi, 32
        mov     BYTE PTR [rdi+4], r8b
        mov     BYTE PTR [rdi+16], sil
        mov     rsi, rax
        shr     rax, 48
        mov     BYTE PTR [rdi+18], al
        mov     rax, rcx
        shr     rsi, 40
        shr     rax, 32
        shr     rcx, 40
        mov     BYTE PTR [rdi+11], r10b
        mov     BYTE PTR [rdi+23], al
        mov     rax, rdx
        shr     rax, 32
        mov     BYTE PTR [rdi+17], sil
        mov     BYTE PTR [rdi+29], al
        mov     rax, rdx
        shr     rdx, 48
        shr     rax, 40
        mov     BYTE PTR [rdi+24], cl
        mov     BYTE PTR [rdi+30], al
        mov     BYTE PTR [rdi+31], dl
        ret
_Z21fiat_25519_from_bytesPmPKh:
        mov     r8, rdi
        movzx   edx, BYTE PTR [rsi+5]
        movzx   edi, BYTE PTR [rsi+6]
        mov     rax, rsi
        movzx   ecx, BYTE PTR [rax+18]
        movzx   r10d, BYTE PTR [rax+30]
        sal     rdx, 40
        sal     rdi, 48
        add     rdi, rdx
        movzx   edx, BYTE PTR [rsi]
        sal     rcx, 42
        add     rdi, rdx
        movzx   edx, BYTE PTR [rsi+4]
        sal     rdx, 32
        add     rdi, rdx
        movzx   edx, BYTE PTR [rsi+3]
        sal     rdx, 24
        add     rdi, rdx
        movzx   edx, BYTE PTR [rsi+2]
        sal     rdx, 16
        add     rdi, rdx
        movzx   edx, BYTE PTR [rsi+1]
        movzx   esi, BYTE PTR [rsi+12]
        sal     rdx, 8
        sal     rsi, 45
        add     rdi, rdx
        movzx   edx, BYTE PTR [rax+11]
        sal     rdx, 37
        add     rsi, rdx
        movzx   edx, BYTE PTR [rax+10]
        sal     rdx, 29
        add     rsi, rdx
        movzx   edx, BYTE PTR [rax+9]
        sal     rdx, 21
        add     rsi, rdx
        movzx   edx, BYTE PTR [rax+8]
        sal     rdx, 13
        add     rsi, rdx
        movzx   edx, BYTE PTR [rax+7]
        sal     rdx, 5
        add     rsi, rdx
        mov     rdx, rdi
        shr     rdx, 51
        add     rsi, rdx
        movzx   edx, BYTE PTR [rax+19]
        sal     rdx, 50
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+17]
        sal     rcx, 34
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+16]
        sal     rcx, 26
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+15]
        sal     rcx, 18
        sal     r10, 36
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+14]
        sal     rcx, 10
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+13]
        lea     r9, [rdx+rcx*4]
        mov     rdx, rsi
        movzx   ecx, BYTE PTR [rax+24]
        shr     rdx, 51
        add     r9, rdx
        movzx   edx, BYTE PTR [rax+25]
        sal     rcx, 39
        sal     rdx, 47
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+23]
        sal     rcx, 31
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+22]
        sal     rcx, 23
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+21]
        sal     rcx, 15
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+20]
        sal     rcx, 7
        add     rdx, rcx
        mov     rcx, r9
        shr     rcx, 51
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+31]
        sal     rcx, 44
        add     rcx, r10
        movzx   r10d, BYTE PTR [rax+29]
        sal     r10, 28
        add     rcx, r10
        movzx   r10d, BYTE PTR [rax+28]
        sal     r10, 20
        add     rcx, r10
        movzx   r10d, BYTE PTR [rax+27]
        movzx   eax, BYTE PTR [rax+26]
        sal     r10, 12
        sal     rax, 4
        add     rcx, r10
        add     rax, rcx
        mov     rcx, rdx
        shr     rcx, 51
        add     rax, rcx
        movabs  rcx, 2251799813685247
        and     rdi, rcx
        and     rsi, rcx
        and     r9, rcx
        and     rdx, rcx
        mov     QWORD PTR [r8], rdi
        mov     QWORD PTR [r8+8], rsi
        mov     QWORD PTR [r8+16], r9
        mov     QWORD PTR [r8+24], rdx
        mov     QWORD PTR [r8+32], rax
        ret
.LC1:
        .quad   4503599627370458
        .quad   4503599627370494