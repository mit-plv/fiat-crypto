_Z24fiat_25519_addcarryx_u51PmPhhmm:
        add     rcx, r8
        movzx   edx, dl
        add     rcx, rdx
        movabs  rax, 2251799813685247
        and     rax, rcx
        mov     QWORD PTR [rdi], rax
        shr     rcx, 51
        mov     BYTE PTR [rsi], cl
        ret
_Z25fiat_25519_subborrowx_u51PmPhhmm:
        movzx   edx, dl
        sub     rcx, rdx
        sub     rcx, r8
        movabs  rax, 2251799813685247
        and     rax, rcx
        mov     QWORD PTR [rdi], rax
        sar     rcx, 51
        neg     ecx
        mov     BYTE PTR [rsi], cl
        ret
_Z22fiat_25519_cmovznz_u64Pmhmm:
        cmp     sil, 1
        sbb     rax, rax
        and     rax, rdx
        test    sil, sil
        mov     edx, 0
        cmove   rcx, rdx
        or      rax, rcx
        mov     QWORD PTR [rdi], rax
        ret
_Z20fiat_25519_carry_mulPmPKmS1_:
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        mov     r14, rdi
        mov     rcx, rsi
        mov     rax, rdx
        mov     rbx, QWORD PTR [rsi+32]
        mov     esi, 0
        mov     QWORD PTR [rsp-104], rbx
        mov     QWORD PTR [rsp-96], rsi
        mov     r15, QWORD PTR [rdx+32]
        lea     rdx, [r15+r15*8]
        lea     rdi, [r15+rdx*2]
        mov     rbp, QWORD PTR [rax+24]
        lea     rdx, [rbp+0+rbp*8]
        lea     r8, [rbp+0+rdx*2]
        mov     rbx, QWORD PTR [rax+16]
        lea     rdx, [rbx+rbx*8]
        lea     r9, [rbx+rdx*2]
        mov     rsi, QWORD PTR [rax+8]
        mov     r11, QWORD PTR [rcx+24]
        mov     r12d, 0
        mov     QWORD PTR [rsp-56], r11
        mov     QWORD PTR [rsp-48], r12
        mov     r11, QWORD PTR [rcx+16]
        mov     r12d, 0
        mov     QWORD PTR [rsp-72], r11
        mov     QWORD PTR [rsp-64], r12
        mov     r11, QWORD PTR [rcx+8]
        mov     r12d, 0
        mov     QWORD PTR [rsp-88], r11
        mov     QWORD PTR [rsp-80], r12
        mov     r12, QWORD PTR [rax]
        mov     r13d, 0
        mov     QWORD PTR [rsp-120], r12
        mov     QWORD PTR [rsp-112], r13
        lea     rax, [rsi+rsi*8]
        lea     rax, [rsi+rax*2]
        mul     QWORD PTR [rcx+32]
        mov     r12, rax
        mov     r13, rdx
        mov     rax, r9
        mul     QWORD PTR [rcx+24]
        mov     r10, r12
        mov     r11, r13
        add     r10, rax
        adc     r11, rdx
        mov     rax, r8
        mul     QWORD PTR [rcx+16]
        add     r10, rax
        adc     r11, rdx
        mov     rax, rdi
        mul     QWORD PTR [rcx+8]
        add     r10, rax
        adc     r11, rdx
        mov     rax, QWORD PTR [rsp-120]
        mul     QWORD PTR [rcx]
        add     r10, rax
        adc     r11, rdx
        mov     QWORD PTR [rsp-40], r10
        mov     QWORD PTR [rsp-32], r11
        mov     rax, QWORD PTR [rsp-104]
        mul     r9
        mov     r10, rax
        mov     r11, rdx
        mov     rax, r8
        mul     QWORD PTR [rcx+24]
        add     r10, rax
        adc     r11, rdx
        mov     rax, rdi
        mul     QWORD PTR [rcx+16]
        add     r10, rax
        adc     r11, rdx
        mov     r12, QWORD PTR [rsp-120]
        mov     rax, r12
        mul     QWORD PTR [rsp-88]
        add     r10, rax
        adc     r11, rdx
        mov     rax, rsi
        mul     QWORD PTR [rcx]
        add     r10, rax
        adc     r11, rdx
        mov     rax, QWORD PTR [rsp-40]
        mov     rdx, QWORD PTR [rsp-32]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     edx, 0
        add     r10, rax
        adc     r11, rdx
        mov     QWORD PTR [rsp-24], r10
        mov     QWORD PTR [rsp-16], r11
        mov     rax, QWORD PTR [rsp-104]
        mul     r8
        mov     r8, rax
        mov     r9, rdx
        mov     rax, rdi
        mul     QWORD PTR [rcx+24]
        add     r8, rax
        adc     r9, rdx
        mov     rax, QWORD PTR [rsp-120]
        mul     QWORD PTR [rsp-72]
        add     r8, rax
        adc     r9, rdx
        mov     rax, QWORD PTR [rsp-88]
        mul     rsi
        add     r8, rax
        adc     r9, rdx
        mov     rax, rbx
        mul     QWORD PTR [rcx]
        add     r8, rax
        adc     r9, rdx
        mov     rax, QWORD PTR [rsp-24]
        mov     rdx, QWORD PTR [rsp-16]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     edx, 0
        add     r8, rax
        adc     r9, rdx
        mov     r12, r8
        mov     r13, r9
        mov     rax, QWORD PTR [rsp-104]
        mul     rdi
        mov     r8, rax
        mov     r9, rdx
        mov     rax, QWORD PTR [rsp-120]
        mul     QWORD PTR [rsp-56]
        add     r8, rax
        adc     r9, rdx
        mov     rax, QWORD PTR [rsp-72]
        mul     rsi
        add     r8, rax
        adc     r9, rdx
        mov     r10, r8
        mov     r11, r9
        mov     rax, QWORD PTR [rsp-88]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        add     r8, r10
        adc     r9, r11
        mov     rax, rbp
        mul     QWORD PTR [rcx]
        add     r8, rax
        adc     r9, rdx
        mov     rax, r12
        mov     rdx, r13
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     edx, 0
        add     r8, rax
        adc     r9, rdx
        mov     rax, QWORD PTR [rsp-120]
        mul     QWORD PTR [rsp-104]
        mov     r10, rax
        mov     r11, rdx
        mov     rax, QWORD PTR [rsp-56]
        mul     rsi
        mov     rsi, rax
        mov     rdi, rdx
        add     rsi, r10
        adc     rdi, r11
        mov     rax, QWORD PTR [rsp-72]
        mul     rbx
        add     rsi, rax
        adc     rdi, rdx
        mov     rax, QWORD PTR [rsp-88]
        mul     rbp
        add     rsi, rax
        adc     rdi, rdx
        mov     rax, r15
        mul     QWORD PTR [rcx]
        add     rax, rsi
        adc     rdx, rdi
        mov     rcx, r8
        mov     rbx, r9
        shrd    rcx, rbx, 51
        shr     rbx, 51
        mov     ebx, 0
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, rax
        shrd    rcx, rdx, 51
        lea     rdx, [rcx+rcx*8]
        lea     rsi, [rcx+rdx*2]
        movabs  rcx, 2251799813685247
        mov     rdx, QWORD PTR [rsp-40]
        and     rdx, rcx
        add     rsi, rdx
        mov     rdx, QWORD PTR [rsp-24]
        and     rdx, rcx
        mov     rdi, rsi
        shr     rdi, 51
        add     rdx, rdi
        and     rsi, rcx
        mov     QWORD PTR [r14], rsi
        mov     rsi, rdx
        and     rsi, rcx
        mov     QWORD PTR [r14+8], rsi
        shr     rdx, 51
        and     r12, rcx
        add     rdx, r12
        mov     QWORD PTR [r14+16], rdx
        and     r8, rcx
        mov     QWORD PTR [r14+24], r8
        and     rax, rcx
        mov     QWORD PTR [r14+32], rax
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
_Z23fiat_25519_carry_squarePmPKm:
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        mov     rbp, rdi
        mov     r12, QWORD PTR [rsi+32]
        mov     r10, QWORD PTR [rsi+24]
        mov     rcx, QWORD PTR [rsi+16]
        mov     rbx, QWORD PTR [rsi+8]
        lea     rax, [r12+r12*8]
        lea     r9, [rax+rax]
        lea     rax, [r9+r12]
        lea     r8, [rax+rax]
        lea     r13, [r10+r10]
        lea     rax, [rcx+rcx]
        mov     QWORD PTR [rsp-16], rax
        mov     rax, QWORD PTR [rsi]
        mov     edx, 0
        mov     QWORD PTR [rsp-72], rax
        mov     QWORD PTR [rsp-64], rdx
        lea     r11, [r10+r10*8]
        add     r11, r11
        lea     rsi, [r11+r10]
        add     rsi, rsi
        mov     rax, rsi
        mul     rcx
        mov     rsi, rax
        mov     rdi, rdx
        mov     rax, r8
        mul     rbx
        add     rsi, rax
        adc     rdi, rdx
        mov     r14, QWORD PTR [rsp-72]
        mov     rax, r14
        mul     QWORD PTR [rsp-72]
        add     rsi, rax
        adc     rdi, rdx
        mov     QWORD PTR [rsp-56], rsi
        mov     QWORD PTR [rsp-48], rdi
        add     r11, r10
        mov     rax, r11
        mul     r10
        mov     rsi, rax
        mov     rdi, rdx
        mov     rax, r8
        mul     rcx
        mov     r14, rsi
        mov     r15, rdi
        add     r14, rax
        adc     r15, rdx
        lea     rsi, [rbx+rbx]
        mov     rax, rsi
        mul     QWORD PTR [rsp-72]
        mov     rsi, rax
        mov     rdi, rdx
        add     rsi, r14
        adc     rdi, r15
        mov     r14, QWORD PTR [rsp-56]
        mov     r15, QWORD PTR [rsp-48]
        shrd    r14, r15, 51
        shr     r15, 51
        mov     edx, 0
        add     rsi, r14
        adc     rdi, rdx
        mov     rax, r8
        mul     r10
        mov     r10, rax
        mov     r11, rdx
        mov     rax, QWORD PTR [rsp-16]
        mul     QWORD PTR [rsp-72]
        add     r10, rax
        adc     r11, rdx
        mov     rax, rbx
        mul     rbx
        add     r10, rax
        adc     r11, rdx
        mov     QWORD PTR [rsp-40], rsi
        mov     QWORD PTR [rsp-32], rdi
        shrd    rsi, rdi, 51
        shr     rdi, 51
        mov     edx, 0
        add     r10, rsi
        adc     r11, rdx
        lea     r14, [r9+r12]
        mov     rax, r14
        mul     r12
        mov     r14, rax
        mov     r15, rdx
        mov     rax, QWORD PTR [rsp-16]
        mul     rbx
        mov     r8, rax
        mov     r9, rdx
        add     r8, r14
        adc     r9, r15
        mov     QWORD PTR [rsp-16], r13
        mov     rax, r13
        mul     QWORD PTR [rsp-72]
        add     r8, rax
        adc     r9, rdx
        mov     r13, r10
        mov     r14, r11
        shrd    r13, r14, 51
        shr     r14, 51
        mov     edx, 0
        add     r8, r13
        adc     r9, rdx
        add     r12, r12
        mov     rax, r12
        mul     QWORD PTR [rsp-72]
        mov     r12, rax
        mov     r13, rdx
        mov     rax, QWORD PTR [rsp-16]
        mul     rbx
        add     r12, rax
        adc     r13, rdx
        mov     rax, rcx
        mul     rcx
        mov     rcx, r12
        mov     rbx, r13
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, r8
        mov     rdx, r9
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     edx, 0
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, rcx
        shrd    rax, rbx, 51
        lea     rdx, [rax+rax*8]
        lea     rdx, [rax+rdx*2]
        movabs  rax, 2251799813685247
        mov     rdi, QWORD PTR [rsp-56]
        and     rdi, rax
        add     rdx, rdi
        mov     rsi, QWORD PTR [rsp-40]
        and     rsi, rax
        mov     rdi, rdx
        shr     rdi, 51
        add     rsi, rdi
        and     rdx, rax
        mov     QWORD PTR [rbp+0], rdx
        mov     rdx, rsi
        and     rdx, rax
        mov     QWORD PTR [rbp+8], rdx
        shr     rsi, 51
        and     r10, rax
        add     rsi, r10
        mov     QWORD PTR [rbp+16], rsi
        and     r8, rax
        mov     QWORD PTR [rbp+24], r8
        and     rcx, rax
        mov     QWORD PTR [rbp+32], rcx
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
_Z29fiat_25519_carry_scmul_121666PmPKm:
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        mov     rcx, rdi
        mov     rbx, rsi
        mov     r10, QWORD PTR [rsi]
        mov     ebp, 121666
        mov     rax, r10
        mul     rbp
        mov     r10, rax
        mov     r11, rdx
        mov     rax, QWORD PTR [rsi+8]
        mul     rbp
        mov     r8, r10
        mov     r9, r11
        shrd    r8, r9, 51
        shr     r9, 51
        mov     r14, r8
        mov     r15, r9
        add     r14, rax
        adc     r15, rdx
        mov     rax, QWORD PTR [rsi+16]
        mul     rbp
        mov     QWORD PTR [rsp-40], r14
        mov     QWORD PTR [rsp-32], r15
        mov     rsi, r14
        mov     rdi, r15
        shrd    rsi, rdi, 51
        shr     rdi, 51
        add     rsi, rax
        adc     rdi, rdx
        mov     rax, QWORD PTR [rbx+24]
        mul     rbp
        mov     QWORD PTR [rsp-24], rsi
        mov     QWORD PTR [rsp-16], rdi
        shrd    rsi, rdi, 51
        shr     rdi, 51
        mov     r12, rsi
        mov     r13, rdi
        add     r12, rax
        adc     r13, rdx
        mov     rax, QWORD PTR [rbx+32]
        mul     rbp
        mov     r14, r12
        mov     r15, r13
        shrd    r14, r15, 51
        shr     r15, 51
        add     r14, rax
        adc     r15, rdx
        mov     rdi, r14
        shrd    rdi, r15, 51
        lea     rdx, [rdi+rdi*8]
        lea     r9, [rdi+rdx*2]
        movabs  rdi, 2251799813685247
        and     r10, rdi
        add     r9, r10
        mov     rdx, r9
        shr     rdx, 51
        mov     r8, QWORD PTR [rsp-40]
        and     r8, rdi
        add     r8, rdx
        and     r9, rdi
        mov     QWORD PTR [rcx], r9
        mov     rdx, r8
        and     rdx, rdi
        mov     QWORD PTR [rcx+8], rdx
        shr     r8, 51
        mov     rsi, QWORD PTR [rsp-24]
        and     rsi, rdi
        add     r8, rsi
        mov     QWORD PTR [rcx+16], r8
        and     r12, rdi
        mov     QWORD PTR [rcx+24], r12
        mov     rax, r14
        and     rax, rdi
        mov     QWORD PTR [rcx+32], rax
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
_Z16fiat_25519_carryPmPKm:
        mov     rdx, rdi
        mov     rax, QWORD PTR [rsi]
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
        add     r8, rax
        mov     rax, r8
        shr     rax, 51
        and     r9, rcx
        add     rax, r9
        and     r8, rcx
        mov     QWORD PTR [rdx], r8
        mov     r8, rax
        and     r8, rcx
        mov     QWORD PTR [rdx+8], r8
        shr     rax, 51
        and     rdi, rcx
        add     rax, rdi
        mov     QWORD PTR [rdx+16], rax
        and     r10, rcx
        mov     QWORD PTR [rdx+24], r10
        and     rsi, rcx
        mov     QWORD PTR [rdx+32], rsi
        ret
_Z14fiat_25519_addPmPKmS1_:
        mov     rax, rdi
        mov     r9, QWORD PTR [rdx+8]
        add     r9, QWORD PTR [rsi+8]
        mov     r8, QWORD PTR [rdx+16]
        add     r8, QWORD PTR [rsi+16]
        mov     rdi, QWORD PTR [rdx+24]
        add     rdi, QWORD PTR [rsi+24]
        mov     rcx, QWORD PTR [rdx+32]
        add     rcx, QWORD PTR [rsi+32]
        mov     rdx, QWORD PTR [rdx]
        add     rdx, QWORD PTR [rsi]
        mov     QWORD PTR [rax], rdx
        mov     QWORD PTR [rax+8], r9
        mov     QWORD PTR [rax+16], r8
        mov     QWORD PTR [rax+24], rdi
        mov     QWORD PTR [rax+32], rcx
        ret
_Z14fiat_25519_subPmPKmS1_:
        mov     rcx, rdi
        mov     rdi, QWORD PTR [rsi+8]
        sub     rdi, QWORD PTR [rdx+8]
        movabs  rax, 4503599627370494
        add     rdi, rax
        mov     r9, rax
        add     r9, QWORD PTR [rsi+16]
        sub     r9, QWORD PTR [rdx+16]
        mov     r8, rax
        add     r8, QWORD PTR [rsi+24]
        sub     r8, QWORD PTR [rdx+24]
        add     rax, QWORD PTR [rsi+32]
        sub     rax, QWORD PTR [rdx+32]
        mov     rsi, QWORD PTR [rsi]
        sub     rsi, QWORD PTR [rdx]
        mov     rdx, rsi
        movabs  rsi, 4503599627370458
        add     rdx, rsi
        mov     QWORD PTR [rcx], rdx
        mov     QWORD PTR [rcx+8], rdi
        mov     QWORD PTR [rcx+16], r9
        mov     QWORD PTR [rcx+24], r8
        mov     QWORD PTR [rcx+32], rax
        ret
_Z14fiat_25519_oppPmPKm:
        movabs  rax, 4503599627370494
        mov     r9, rax
        sub     r9, QWORD PTR [rsi+8]
        mov     r8, rax
        sub     r8, QWORD PTR [rsi+16]
        mov     rcx, rax
        sub     rcx, QWORD PTR [rsi+24]
        sub     rax, QWORD PTR [rsi+32]
        movabs  rdx, 4503599627370458
        sub     rdx, QWORD PTR [rsi]
        mov     QWORD PTR [rdi], rdx
        mov     QWORD PTR [rdi+8], r9
        mov     QWORD PTR [rdi+16], r8
        mov     QWORD PTR [rdi+24], rcx
        mov     QWORD PTR [rdi+32], rax
        ret
_Z20fiat_25519_selectznzPmhPKmS1_:
        push    rbp
        push    rbx
        mov     r8, rdx
        cmp     sil, 1
        sbb     rdx, rdx
        mov     eax, 0
        test    sil, sil
        mov     rbx, rax
        cmovne  rbx, QWORD PTR [rcx+8]
        mov     r9, rdx
        and     r9, QWORD PTR [r8+8]
        or      rbx, r9
        test    sil, sil
        mov     r11, rax
        cmovne  r11, QWORD PTR [rcx+16]
        mov     r9, rdx
        and     r9, QWORD PTR [r8+16]
        or      r11, r9
        test    sil, sil
        mov     r10, rax
        cmovne  r10, QWORD PTR [rcx+24]
        mov     r9, rdx
        and     r9, QWORD PTR [r8+24]
        or      r10, r9
        test    sil, sil
        mov     r9, rax
        cmovne  r9, QWORD PTR [rcx+32]
        mov     rbp, rdx
        and     rbp, QWORD PTR [r8+32]
        or      r9, rbp
        test    sil, sil
        cmovne  rax, QWORD PTR [rcx]
        and     rdx, QWORD PTR [r8]
        or      rax, rdx
        mov     QWORD PTR [rdi], rax
        mov     QWORD PTR [rdi+8], rbx
        mov     QWORD PTR [rdi+16], r11
        mov     QWORD PTR [rdi+24], r10
        mov     QWORD PTR [rdi+32], r9
        pop     rbx
        pop     rbp
        ret
_Z19fiat_25519_to_bytesPhPKm:
        push    rbp
        push    rbx
        mov     rax, rdi
        movabs  rbx, -2251799813685229
        add     rbx, QWORD PTR [rsi]
        mov     rdx, rbx
        sar     rdx, 51
        neg     edx
        movzx   edx, dl
        mov     rdi, QWORD PTR [rsi+8]
        sub     rdi, rdx
        movabs  rdx, -2251799813685247
        add     rdi, rdx
        mov     r8, rdi
        sar     r8, 51
        neg     r8d
        movzx   r8d, r8b
        mov     rcx, rdx
        add     rcx, QWORD PTR [rsi+16]
        sub     rcx, r8
        mov     r11, rcx
        sar     rcx, 51
        neg     ecx
        movzx   ecx, cl
        mov     r8, rdx
        add     r8, QWORD PTR [rsi+24]
        sub     r8, rcx
        mov     rcx, r8
        sar     rcx, 51
        neg     ecx
        movzx   ecx, cl
        add     rdx, QWORD PTR [rsi+32]
        sub     rdx, rcx
        mov     rbp, rdx
        sar     rbp, 51
        mov     r10d, 0
        test    bpl, bpl
        movabs  rcx, 2251799813685229
        cmove   rcx, r10
        movabs  r9, 2251799813685247
        and     rbx, r9
        add     rcx, rbx
        mov     rsi, rcx
        and     rsi, r9
        test    bpl, bpl
        cmovne  r10, r9
        and     rdi, r9
        add     rdi, r10
        shr     rcx, 51
        add     rdi, rcx
        mov     rcx, r11
        and     rcx, r9
        add     rcx, r10
        mov     r11, rdi
        shr     r11, 51
        add     rcx, r11
        and     r8, r9
        add     r8, r10
        mov     r11, rcx
        shr     r11, 51
        add     r8, r11
        sal     rdi, 3
        movabs  r11, 18014398509481976
        and     rdi, r11
        mov     r11, rsi
        shr     r11, 48
        lea     rbp, [rdi+r11]
        sal     rcx, 6
        movabs  r11, 144115188075855808
        and     rcx, r11
        shr     rdi, 48
        add     rcx, rdi
        mov     r11, r8
        and     r11, r9
        mov     rdi, rcx
        shr     rdi, 56
        lea     rdi, [rdi+r11*2]
        and     rdx, r9
        add     rdx, r10
        shr     r8, 51
        add     rdx, r8
        sal     rdx, 4
        movabs  r8, 36028797018963952
        and     rdx, r8
        mov     r8, rdi
        shr     r8, 48
        add     rdx, r8
        mov     BYTE PTR [rax], sil
        mov     rbx, rsi
        mov     BYTE PTR [rax+1], bh
        mov     r8, rsi
        shr     r8, 16
        mov     BYTE PTR [rax+2], r8b
        mov     r8, rsi
        shr     r8, 24
        mov     BYTE PTR [rax+3], r8b
        mov     r8, rsi
        shr     r8, 32
        mov     BYTE PTR [rax+4], r8b
        shr     rsi, 40
        mov     BYTE PTR [rax+5], sil
        mov     BYTE PTR [rax+6], bpl
        mov     rbx, rbp
        mov     BYTE PTR [rax+7], bh
        shr     rbx, 16
        mov     BYTE PTR [rax+8], bl
        mov     rbx, rbp
        shr     rbx, 24
        mov     BYTE PTR [rax+9], bl
        mov     rbx, rbp
        shr     rbx, 32
        mov     BYTE PTR [rax+10], bl
        mov     rbx, rbp
        shr     rbx, 40
        mov     BYTE PTR [rax+11], bl
        mov     BYTE PTR [rax+12], cl
        mov     BYTE PTR [rax+13], ch
        mov     rsi, rcx
        shr     rsi, 16
        mov     BYTE PTR [rax+14], sil
        mov     rsi, rcx
        shr     rsi, 24
        mov     BYTE PTR [rax+15], sil
        mov     rsi, rcx
        shr     rsi, 32
        mov     BYTE PTR [rax+16], sil
        mov     rsi, rcx
        shr     rsi, 40
        mov     BYTE PTR [rax+17], sil
        shr     rcx, 48
        mov     BYTE PTR [rax+18], cl
        mov     BYTE PTR [rax+19], dil
        mov     rbx, rdi
        mov     BYTE PTR [rax+20], bh
        mov     rcx, rdi
        shr     rcx, 16
        mov     BYTE PTR [rax+21], cl
        mov     rcx, rdi
        shr     rcx, 24
        mov     BYTE PTR [rax+22], cl
        mov     rcx, rdi
        shr     rcx, 32
        mov     BYTE PTR [rax+23], cl
        shr     rdi, 40
        mov     BYTE PTR [rax+24], dil
        mov     BYTE PTR [rax+25], dl
        mov     BYTE PTR [rax+26], dh
        mov     rcx, rdx
        shr     rcx, 16
        mov     BYTE PTR [rax+27], cl
        mov     rcx, rdx
        shr     rcx, 24
        mov     BYTE PTR [rax+28], cl
        mov     rcx, rdx
        shr     rcx, 32
        mov     BYTE PTR [rax+29], cl
        mov     rcx, rdx
        shr     rcx, 40
        mov     BYTE PTR [rax+30], cl
        shr     rdx, 48
        mov     BYTE PTR [rax+31], dl
        pop     rbx
        pop     rbp
        ret
_Z21fiat_25519_from_bytesPmPKh:
        mov     r8, rdi
        mov     rax, rsi
        movzx   edi, BYTE PTR [rsi+6]
        sal     rdi, 48
        movzx   edx, BYTE PTR [rsi+5]
        sal     rdx, 40
        add     rdi, rdx
        movzx   edx, BYTE PTR [rsi]
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
        sal     rdx, 8
        add     rdi, rdx
        movzx   esi, BYTE PTR [rsi+12]
        sal     rsi, 45
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
        movzx   ecx, BYTE PTR [rax+18]
        sal     rcx, 42
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+17]
        sal     rcx, 34
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+16]
        sal     rcx, 26
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+15]
        sal     rcx, 18
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+14]
        sal     rcx, 10
        add     rdx, rcx
        movzx   ecx, BYTE PTR [rax+13]
        lea     r9, [rdx+rcx*4]
        mov     rdx, rsi
        shr     rdx, 51
        add     r9, rdx
        movzx   edx, BYTE PTR [rax+25]
        sal     rdx, 47
        movzx   ecx, BYTE PTR [rax+24]
        sal     rcx, 39
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
        movzx   r10d, BYTE PTR [rax+30]
        sal     r10, 36
        add     rcx, r10
        movzx   r10d, BYTE PTR [rax+29]
        sal     r10, 28
        add     rcx, r10
        movzx   r10d, BYTE PTR [rax+28]
        sal     r10, 20
        add     rcx, r10
        movzx   r10d, BYTE PTR [rax+27]
        sal     r10, 12
        add     rcx, r10
        movzx   eax, BYTE PTR [rax+26]
        sal     rax, 4
        add     rax, rcx
        mov     rcx, rdx
        shr     rcx, 51
        add     rax, rcx
        movabs  rcx, 2251799813685247
        and     rdi, rcx
        mov     QWORD PTR [r8], rdi
        and     rsi, rcx
        mov     QWORD PTR [r8+8], rsi
        and     r9, rcx
        mov     QWORD PTR [r8+16], r9
        and     rdx, rcx
        mov     QWORD PTR [r8+24], rdx
        mov     QWORD PTR [r8+32], rax
        ret