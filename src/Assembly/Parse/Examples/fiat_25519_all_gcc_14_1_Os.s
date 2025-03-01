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
        push    r14
        push    r13
        push    r12
        xor     r12d, r12d
        push    rbp
        push    rbx
        sub     rsp, 32
        mov     r11, QWORD PTR [rcx+24]
        mov     rbx, QWORD PTR [rsi+32]
        xor     esi, esi
        mov     rax, QWORD PTR [rdx]
        mov     rbp, QWORD PTR [rdx+16]
        mov     QWORD PTR [rsp-48], r12
        xor     r12d, r12d
        mov     r14, QWORD PTR [rdx+24]
        mov     r15, QWORD PTR [rdx+32]
        mov     QWORD PTR [rsp-56], r11
        mov     r11, QWORD PTR [rcx+16]
        mov     QWORD PTR [rsp-104], rbx
        imul    r9, rbp, 19
        mov     rbx, QWORD PTR [rdx+8]
        mov     QWORD PTR [rsp-64], r12
        xor     edx, edx
        xor     r12d, r12d
        mov     QWORD PTR [rsp-72], r11
        mov     r11, QWORD PTR [rcx+8]
        imul    r8, r14, 19
        mov     QWORD PTR [rsp-96], rsi
        imul    rsi, r15, 19
        mov     QWORD PTR [rsp-88], r11
        mov     QWORD PTR [rsp-80], r12
        mov     QWORD PTR [rsp-120], rax
        mov     QWORD PTR [rsp-112], rdx
        mov     rax, QWORD PTR [rcx]
        xor     edx, edx
        mov     QWORD PTR [rsp+16], rdx
        mov     QWORD PTR [rsp+8], rax
        imul    rax, rbx, 19
        mul     QWORD PTR [rcx+32]
        mov     r12, rax
        mov     r13, rdx
        mov     rax, r9
        mul     QWORD PTR [rcx+24]
        add     r12, rax
        mov     rax, r8
        adc     r13, rdx
        mul     QWORD PTR [rcx+16]
        add     r12, rax
        mov     rax, rsi
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
        mov     rax, rsi
        adc     r11, rdx
        mul     QWORD PTR [rcx+16]
        add     r10, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r11, rdx
        mul     QWORD PTR [rsp-88]
        mov     r12, r10
        mov     r10, QWORD PTR [rsp-40]
        mov     r13, r11
        mov     r11, QWORD PTR [rsp-32]
        add     r12, rax
        mov     rax, rbx
        adc     r13, rdx
        mul     QWORD PTR [rcx]
        add     rax, r12
        adc     rdx, r13
        shrd    r10, r11, 51
        xor     r11d, r11d
        add     rax, r10
        mov     QWORD PTR [rsp-24], rax
        mov     rax, QWORD PTR [rsp-104]
        adc     rdx, r11
        mov     QWORD PTR [rsp-16], rdx
        mul     r8
        mov     r8, rax
        mov     r9, rdx
        mov     rax, rsi
        mul     QWORD PTR [rcx+24]
        add     r8, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r9, rdx
        mul     QWORD PTR [rsp-72]
        add     r8, rax
        mov     rax, QWORD PTR [rsp-88]
        adc     r9, rdx
        mov     r10, r8
        mul     rbx
        mov     r11, r9
        mov     r8, rax
        mov     r9, rdx
        mov     rax, rbp
        add     r8, r10
        adc     r9, r11
        mul     QWORD PTR [rcx]
        add     r8, rax
        mov     rax, QWORD PTR [rsp-24]
        adc     r9, rdx
        mov     rdx, QWORD PTR [rsp-16]
        shrd    rax, rdx, 51
        xor     edx, edx
        add     r8, rax
        mov     rax, QWORD PTR [rsp-104]
        adc     r9, rdx
        mov     QWORD PTR [rsp-8], r8
        mul     rsi
        mov     QWORD PTR [rsp], r9
        movabs  rsi, 2251799813685247
        mov     r12, rax
        mov     r13, rdx
        mov     rax, QWORD PTR [rsp-120]
        mul     QWORD PTR [rsp-56]
        add     r12, rax
        mov     rax, QWORD PTR [rsp-72]
        adc     r13, rdx
        mul     rbx
        add     r12, rax
        mov     rax, QWORD PTR [rsp-88]
        adc     r13, rdx
        mul     rbp
        add     r12, rax
        mov     rax, r14
        adc     r13, rdx
        mul     QWORD PTR [rcx]
        mov     r10, rax
        mov     r11, rdx
        mov     rax, r8
        mov     r8, QWORD PTR [rsp-8]
        add     r10, r12
        adc     r11, r13
        shrd    rax, r9, 51
        xor     edx, edx
        add     r10, rax
        mov     rax, QWORD PTR [rsp-120]
        adc     r11, rdx
        mul     QWORD PTR [rsp-104]
        mov     r12, rax
        mov     rax, QWORD PTR [rsp-56]
        mov     r13, rdx
        mov     rcx, r12
        mul     rbx
        mov     rbx, r13
        add     rcx, rax
        mov     rax, QWORD PTR [rsp-72]
        adc     rbx, rdx
        mul     rbp
        add     rcx, rax
        mov     rax, QWORD PTR [rsp-88]
        adc     rbx, rdx
        mul     r14
        add     rcx, rax
        mov     rax, QWORD PTR [rsp+8]
        adc     rbx, rdx
        mul     r15
        add     rax, rcx
        mov     rcx, r10
        adc     rdx, rbx
        shrd    rcx, r11, 51
        xor     ebx, ebx
        add     rax, rcx
        adc     rdx, rbx
        mov     r14, rax
        and     r8, rsi
        and     r10, rsi
        shrd    rax, rdx, 51
        mov     rdx, QWORD PTR [rsp-40]
        mov     QWORD PTR [rdi+24], r10
        imul    rcx, rax, 19
        mov     rax, r14
        and     rdx, rsi
        and     rax, rsi
        mov     QWORD PTR [rdi+32], rax
        add     rcx, rdx
        mov     rdx, QWORD PTR [rsp-24]
        mov     r9, rcx
        and     rcx, rsi
        and     rdx, rsi
        shr     r9, 51
        mov     QWORD PTR [rdi], rcx
        add     rdx, r9
        mov     rcx, rdx
        shr     rdx, 51
        and     rcx, rsi
        add     rdx, r8
        mov     QWORD PTR [rdi+8], rcx
        mov     QWORD PTR [rdi+16], rdx
        add     rsp, 32
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        ret
_Z23fiat_25519_carry_squarePmPKm:
        push    r15
        mov     r10, rdi
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        mov     r8, QWORD PTR [rsi+24]
        mov     r14, QWORD PTR [rsi]
        mov     rcx, QWORD PTR [rsi+16]
        mov     r11, QWORD PTR [rsi+8]
        mov     rbx, QWORD PTR [rsi+32]
        imul    rsi, r8, 38
        lea     rax, [r8+r8]
        mov     QWORD PTR [rsp-24], rax
        lea     rax, [rcx+rcx]
        mov     QWORD PTR [rsp-16], rax
        imul    r9, rbx, 38
        mov     rax, rsi
        mul     rcx
        mov     rsi, rax
        mov     rax, r9
        mov     rdi, rdx
        mul     r11
        add     rsi, rax
        mov     rax, r14
        adc     rdi, rdx
        mul     r14
        add     rsi, rax
        adc     rdi, rdx
        mov     r12, rsi
        imul    rsi, r8, 19
        mov     r13, rdi
        mov     rax, rsi
        mul     r8
        mov     rsi, rax
        mov     rax, r9
        mov     rdi, rdx
        mul     rcx
        add     rsi, rax
        lea     rax, [r11+r11]
        adc     rdi, rdx
        mul     r14
        add     rsi, rax
        mov     rax, r12
        adc     rdi, rdx
        shrd    rax, r13, 51
        xor     edx, edx
        add     rsi, rax
        mov     rax, r9
        adc     rdi, rdx
        mul     r8
        mov     QWORD PTR [rsp-56], rsi
        mov     QWORD PTR [rsp-48], rdi
        mov     r8, rax
        mov     rax, QWORD PTR [rsp-16]
        mov     r9, rdx
        mul     r14
        add     r8, rax
        mov     rax, r11
        adc     r9, rdx
        mul     r11
        add     r8, rax
        mov     rax, rsi
        mov     rsi, QWORD PTR [rsp-56]
        adc     r9, rdx
        shrd    rax, rdi, 51
        xor     edx, edx
        add     r8, rax
        adc     r9, rdx
        imul    rax, rbx, 19
        mov     QWORD PTR [rsp-40], r8
        mov     QWORD PTR [rsp-32], r9
        mul     rbx
        mov     rdi, rax
        mov     rax, QWORD PTR [rsp-16]
        mov     rbp, rdx
        mul     r11
        add     rdi, rax
        mov     rax, QWORD PTR [rsp-24]
        adc     rbp, rdx
        mul     r14
        add     rdi, rax
        mov     rax, r8
        mov     r8, QWORD PTR [rsp-40]
        adc     rbp, rdx
        shrd    rax, r9, 51
        xor     edx, edx
        add     rdi, rax
        adc     rbp, rdx
        add     rbx, rbx
        mov     rax, rbx
        mul     r14
        mov     r14, rax
        mov     rax, QWORD PTR [rsp-24]
        mov     r15, rdx
        mul     r11
        add     r14, rax
        mov     rax, rcx
        adc     r15, rdx
        mul     rcx
        mov     rcx, rax
        mov     rbx, rdx
        mov     rax, rdi
        add     rcx, r14
        adc     rbx, r15
        shrd    rax, rbp, 51
        xor     edx, edx
        add     rcx, rax
        adc     rbx, rdx
        mov     rax, rcx
        movabs  rdx, 2251799813685247
        shrd    rax, rbx, 51
        and     r12, rdx
        and     rsi, rdx
        and     r8, rdx
        imul    rax, rax, 19
        and     rdi, rdx
        and     rcx, rdx
        add     rax, r12
        mov     r9, rax
        and     rax, rdx
        shr     r9, 51
        mov     QWORD PTR [r10], rax
        add     rsi, r9
        mov     rax, rsi
        shr     rsi, 51
        and     rax, rdx
        add     rsi, r8
        mov     QWORD PTR [r10+8], rax
        mov     QWORD PTR [r10+16], rsi
        mov     QWORD PTR [r10+24], rdi
        pop     rbx
        mov     QWORD PTR [r10+32], rcx
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
        mov     r12, rsi
        mul     r11
        mov     r13, rdi
        shrd    r12, rdi, 51
        shr     r13, 51
        add     r12, rax
        mov     rax, QWORD PTR [r10+32]
        adc     r13, rdx
        mov     r10, r12
        mul     r11
        shrd    r10, r13, 51
        mov     r11, r13
        shr     r11, 51
        add     rax, r10
        adc     rdx, r11
        mov     QWORD PTR [rsp-24], rax
        shrd    rax, rdx, 51
        mov     QWORD PTR [rsp-16], rdx
        imul    r10, rax, 19
        movabs  rax, 2251799813685247
        and     r14, rax
        and     r8, rax
        and     rsi, rax
        and     r12, rax
        mov     QWORD PTR [rcx+24], r12
        add     r10, r14
        mov     rdx, r10
        and     r10, rax
        shr     rdx, 51
        mov     QWORD PTR [rcx], r10
        add     r8, rdx
        mov     rdx, r8
        shr     r8, 51
        and     rdx, rax
        add     r8, rsi
        and     rax, QWORD PTR [rsp-24]
        pop     r12
        mov     QWORD PTR [rcx+8], rdx
        pop     r13
        mov     QWORD PTR [rcx+16], r8
        pop     r14
        mov     QWORD PTR [rcx+32], rax
        pop     r15
        ret
_Z16fiat_25519_carryPmPKm:
        mov     rax, QWORD PTR [rsi]
        mov     rcx, rdi
        mov     r9, rax
        shr     r9, 51
        add     r9, QWORD PTR [rsi+8]
        mov     r8, r9
        shr     r8, 51
        add     r8, QWORD PTR [rsi+16]
        mov     r10, r8
        shr     r10, 51
        add     r10, QWORD PTR [rsi+24]
        mov     rdi, r10
        shr     rdi, 51
        add     rdi, QWORD PTR [rsi+32]
        movabs  rsi, 2251799813685247
        mov     rdx, rdi
        and     rax, rsi
        and     r9, rsi
        and     r8, rsi
        shr     rdx, 51
        and     r10, rsi
        and     rdi, rsi
        imul    rdx, rdx, 19
        mov     QWORD PTR [rcx+24], r10
        mov     QWORD PTR [rcx+32], rdi
        add     rdx, rax
        mov     rax, rdx
        and     rdx, rsi
        shr     rax, 51
        mov     QWORD PTR [rcx], rdx
        add     rax, r9
        mov     rdx, rax
        shr     rax, 51
        and     rdx, rsi
        add     rax, r8
        mov     QWORD PTR [rcx+8], rdx
        mov     QWORD PTR [rcx+16], rax
        ret
_Z14fiat_25519_addPmPKmS1_:
        mov     r9, QWORD PTR [rdx+8]
        mov     r8, QWORD PTR [rdx+16]
        mov     rax, rdi
        mov     rcx, QWORD PTR [rdx+32]
        mov     rdi, QWORD PTR [rdx+24]
        add     r9, QWORD PTR [rsi+8]
        mov     rdx, QWORD PTR [rdx]
        add     r8, QWORD PTR [rsi+16]
        add     rdi, QWORD PTR [rsi+24]
        add     rcx, QWORD PTR [rsi+32]
        add     rdx, QWORD PTR [rsi]
        mov     QWORD PTR [rax+8], r9
        mov     QWORD PTR [rax], rdx
        mov     QWORD PTR [rax+16], r8
        mov     QWORD PTR [rax+24], rdi
        mov     QWORD PTR [rax+32], rcx
        ret
_Z14fiat_25519_subPmPKmS1_:
        mov     r9, QWORD PTR [rsi+16]
        mov     r8, QWORD PTR [rsi+24]
        mov     rcx, rdi
        movabs  rax, 4503599627370494
        mov     rdi, QWORD PTR [rsi+8]
        sub     rdi, QWORD PTR [rdx+8]
        add     rdi, rax
        add     r9, rax
        add     r8, rax
        add     rax, QWORD PTR [rsi+32]
        mov     rsi, QWORD PTR [rsi]
        sub     rsi, QWORD PTR [rdx]
        sub     r9, QWORD PTR [rdx+16]
        sub     r8, QWORD PTR [rdx+24]
        sub     rax, QWORD PTR [rdx+32]
        mov     rdx, rsi
        mov     QWORD PTR [rcx+8], rdi
        movabs  rsi, 4503599627370458
        add     rdx, rsi
        mov     QWORD PTR [rcx+16], r9
        mov     QWORD PTR [rcx], rdx
        mov     QWORD PTR [rcx+24], r8
        mov     QWORD PTR [rcx+32], rax
        ret
_Z14fiat_25519_oppPmPKm:
        movabs  rax, 4503599627370494
        movabs  rdx, 4503599627370458
        sub     rdx, QWORD PTR [rsi]
        mov     r9, rax
        mov     r8, rax
        sub     r9, QWORD PTR [rsi+8]
        sub     r8, QWORD PTR [rsi+16]
        mov     rcx, rax
        sub     rax, QWORD PTR [rsi+32]
        sub     rcx, QWORD PTR [rsi+24]
        mov     QWORD PTR [rdi], rdx
        mov     QWORD PTR [rdi+8], r9
        mov     QWORD PTR [rdi+16], r8
        mov     QWORD PTR [rdi+24], rcx
        mov     QWORD PTR [rdi+32], rax
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
        shr     r10, 48
        add     r10, rcx
        shr     rcx, 48
        add     rax, rcx
        mov     rcx, r11
        shr     r11, 51
        mov     DWORD PTR [rdi+6], r10d
        and     rcx, r8
        mov     rbx, rax
        add     rdx, r11
        mov     DWORD PTR [rdi+12], eax
        shr     rbx, 56
        add     rcx, rcx
        sal     rdx, 4
        movabs  r8, 36028797018963952
        add     rcx, rbx
        and     rdx, r8
        pop     rbx
        pop     rbp
        mov     r8, rcx
        mov     DWORD PTR [rdi+19], ecx
        shr     r8, 48
        add     rdx, r8
        mov     r8, rsi
        shr     r8, 32
        shr     rsi, 40
        mov     DWORD PTR [rdi+25], edx
        mov     BYTE PTR [rdi+5], sil
        mov     rsi, r10
        shr     r10, 40
        shr     rsi, 32
        mov     BYTE PTR [rdi+4], r8b
        mov     BYTE PTR [rdi+10], sil
        mov     rsi, rax
        shr     rsi, 32
        mov     BYTE PTR [rdi+11], r10b
        mov     BYTE PTR [rdi+16], sil
        mov     rsi, rax
        shr     rax, 48
        mov     BYTE PTR [rdi+18], al
        mov     rax, rcx
        shr     rsi, 40
        shr     rax, 32
        shr     rcx, 40
        mov     BYTE PTR [rdi+17], sil
        mov     BYTE PTR [rdi+23], al
        mov     rax, rdx
        shr     rax, 32
        mov     BYTE PTR [rdi+24], cl
        mov     BYTE PTR [rdi+29], al
        mov     rax, rdx
        shr     rdx, 48
        shr     rax, 40
        mov     BYTE PTR [rdi+31], dl
        mov     BYTE PTR [rdi+30], al
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