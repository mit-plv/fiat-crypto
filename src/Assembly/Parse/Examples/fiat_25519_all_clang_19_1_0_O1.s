_Z24fiat_25519_addcarryx_u51PmPhhmm:
        mov     eax, edx
        add     rcx, r8
        add     rcx, rax
        movabs  rax, 2251799813685247
        and     rax, rcx
        shr     rcx, 51
        mov     qword ptr [rdi], rax
        mov     byte ptr [rsi], cl
        ret

_Z25fiat_25519_subborrowx_u51PmPhhmm:
        mov     eax, edx
        add     rax, r8
        sub     rcx, rax
        movabs  rax, 2251799813685247
        and     rax, rcx
        mov     qword ptr [rdi], rax
        shr     rcx, 51
        neg     cl
        mov     byte ptr [rsi], cl
        ret

_Z22fiat_25519_cmovznz_u64Pmhmm:
        test    esi, esi
        cmovne  rdx, rcx
        mov     qword ptr [rdi], rdx
        ret

_Z20fiat_25519_carry_mulPmPKmS1_:
        push    rbp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        sub     rsp, 192
        mov     r8, rdx
        mov     r15, qword ptr [rsi + 32]
        mov     r13, rsi
        mov     qword ptr [rsp - 104], rsi
        mov     rcx, qword ptr [rdx + 32]
        mov     qword ptr [rsp - 96], rcx
        lea     rax, [rcx + 8*rcx]
        lea     rbx, [rcx + 2*rax]
        mov     rax, rbx
        mul     r15
        mov     qword ptr [rsp + 176], rax
        mov     qword ptr [rsp + 184], rdx
        mov     rcx, qword ptr [r8 + 24]
        mov     qword ptr [rsp - 120], rcx
        lea     rax, [rcx + 8*rcx]
        lea     r9, [rcx + 2*rax]
        mov     rax, r9
        mul     r15
        mov     qword ptr [rsp + 144], rax
        mov     qword ptr [rsp + 152], rdx
        mov     rcx, qword ptr [r8 + 16]
        mov     qword ptr [rsp - 128], rcx
        lea     rax, [rcx + 8*rcx]
        lea     r10, [rcx + 2*rax]
        mov     rax, r10
        mul     r15
        mov     qword ptr [rsp + 128], rax
        mov     qword ptr [rsp + 136], rdx
        mov     rcx, qword ptr [r8 + 8]
        lea     rax, [rcx + 8*rcx]
        lea     rax, [rcx + 2*rax]
        mul     r15
        mov     qword ptr [rsp + 56], rax
        mov     qword ptr [rsp + 64], rdx
        mov     r14, qword ptr [rsi + 24]
        mov     rax, r14
        mul     rbx
        mov     r11, rdx
        mov     qword ptr [rsp + 40], rax
        mov     rax, r14
        mul     r9
        mov     rbp, rdx
        mov     rsi, rax
        mov     rax, r14
        mul     r10
        mov     qword ptr [rsp + 16], rax
        mov     r12, rdx
        mov     r10, qword ptr [r13 + 16]
        mov     rax, r10
        mul     rbx
        mov     qword ptr [rsp + 72], rdx
        mov     qword ptr [rsp + 48], rax
        mov     rax, r10
        mul     r9
        mov     qword ptr [rsp - 16], rax
        mov     qword ptr [rsp - 8], rdx
        mov     r9, qword ptr [r13 + 8]
        mov     rax, r9
        mul     rbx
        mov     qword ptr [rsp - 32], rax
        mov     qword ptr [rsp - 24], rdx
        mov     r8, qword ptr [r8]
        mov     rax, r8
        mul     r15
        mov     qword ptr [rsp + 168], rdx
        mov     qword ptr [rsp + 160], rax
        mov     rax, r14
        mov     r15, rcx
        mov     qword ptr [rsp - 112], rcx
        mul     rcx
        mov     qword ptr [rsp + 120], rdx
        mov     qword ptr [rsp + 112], rax
        mov     rax, r8
        mov     qword ptr [rsp - 88], r8
        mul     r14
        mov     qword ptr [rsp + 104], rdx
        mov     qword ptr [rsp + 96], rax
        mov     rax, r10
        mov     rcx, qword ptr [rsp - 128]
        mul     rcx
        mov     r13, rdx
        mov     rbx, rax
        mov     rax, r10
        mul     r15
        mov     r15, rdx
        mov     r14, rax
        mov     rax, r8
        mul     r10
        mov     qword ptr [rsp + 8], rdx
        mov     qword ptr [rsp], rax
        mov     rax, r9
        mul     qword ptr [rsp - 120]
        mov     qword ptr [rsp + 88], rdx
        mov     qword ptr [rsp + 80], rax
        mov     rax, r9
        mul     rcx
        mov     qword ptr [rsp + 32], rdx
        mov     qword ptr [rsp + 24], rax
        mov     rax, r9
        mov     r8, qword ptr [rsp - 112]
        mul     r8
        mov     qword ptr [rsp - 56], rax
        mov     qword ptr [rsp - 48], rdx
        mov     rax, qword ptr [rsp - 104]
        mov     r10, qword ptr [rax]
        mov     rcx, qword ptr [rsp - 88]
        mov     rax, rcx
        mul     r9
        mov     qword ptr [rsp - 72], rdx
        mov     qword ptr [rsp - 80], rax
        mov     rax, r10
        mul     qword ptr [rsp - 96]
        mov     qword ptr [rsp - 96], rdx
        mov     qword ptr [rsp - 104], rax
        mov     rax, r10
        mul     qword ptr [rsp - 120]
        mov     qword ptr [rsp - 120], rdx
        mov     qword ptr [rsp - 40], rax
        mov     rax, r10
        mul     qword ptr [rsp - 128]
        mov     qword ptr [rsp - 128], rdx
        mov     qword ptr [rsp - 64], rax
        mov     rax, r10
        mul     r8
        mov     qword ptr [rsp - 112], rdx
        mov     r9, rax
        mov     rax, r10
        mul     rcx
        mov     r8, qword ptr [rsp + 16]
        add     r8, qword ptr [rsp + 56]
        adc     r12, qword ptr [rsp + 64]
        add     r8, qword ptr [rsp - 16]
        adc     r12, qword ptr [rsp - 8]
        add     r8, qword ptr [rsp - 32]
        adc     r12, qword ptr [rsp - 24]
        add     r8, rax
        adc     r12, rdx
        shld    r12, r8, 13
        movabs  rax, 2251799813685247
        and     r8, rax
        mov     rcx, qword ptr [rsp + 40]
        add     rcx, qword ptr [rsp + 144]
        adc     r11, qword ptr [rsp + 152]
        add     rsi, qword ptr [rsp + 128]
        adc     rbp, qword ptr [rsp + 136]
        add     rsi, qword ptr [rsp + 48]
        adc     rbp, qword ptr [rsp + 72]
        add     rsi, qword ptr [rsp - 80]
        adc     rbp, qword ptr [rsp - 72]
        add     rsi, r9
        adc     rbp, qword ptr [rsp - 112]
        add     rsi, r12
        adc     rbp, 0
        shld    rbp, rsi, 13
        and     rsi, rax
        add     rcx, qword ptr [rsp - 56]
        adc     r11, qword ptr [rsp - 48]
        add     rcx, qword ptr [rsp]
        adc     r11, qword ptr [rsp + 8]
        add     rcx, qword ptr [rsp - 64]
        adc     r11, qword ptr [rsp - 128]
        add     rcx, rbp
        adc     r11, 0
        shld    r11, rcx, 13
        and     rcx, rax
        add     r14, qword ptr [rsp + 176]
        adc     r15, qword ptr [rsp + 184]
        add     r14, qword ptr [rsp + 24]
        adc     r15, qword ptr [rsp + 32]
        add     r14, qword ptr [rsp + 96]
        adc     r15, qword ptr [rsp + 104]
        add     r14, qword ptr [rsp - 40]
        adc     r15, qword ptr [rsp - 120]
        add     r14, r11
        adc     r15, 0
        shld    r15, r14, 13
        and     r14, rax
        add     rbx, qword ptr [rsp + 112]
        adc     r13, qword ptr [rsp + 120]
        add     rbx, qword ptr [rsp + 80]
        adc     r13, qword ptr [rsp + 88]
        add     rbx, qword ptr [rsp + 160]
        adc     r13, qword ptr [rsp + 168]
        add     rbx, qword ptr [rsp - 104]
        adc     r13, qword ptr [rsp - 96]
        add     rbx, r15
        adc     r13, 0
        shld    r13, rbx, 13
        lea     rdx, [8*r13]
        add     rdx, r13
        lea     rdx, [2*rdx]
        add     rdx, r13
        add     rdx, r8
        mov     r8, rdx
        shr     r8, 51
        add     r8, rsi
        mov     rsi, r8
        shr     rsi, 51
        add     rsi, rcx
        and     rbx, rax
        and     rdx, rax
        and     r8, rax
        mov     qword ptr [rdi], rdx
        mov     qword ptr [rdi + 8], r8
        mov     qword ptr [rdi + 16], rsi
        mov     qword ptr [rdi + 24], r14
        mov     qword ptr [rdi + 32], rbx
        add     rsp, 192
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret

_Z23fiat_25519_carry_squarePmPKm:
        push    rbp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        push    rax
        mov     rdx, qword ptr [rsi + 32]
        lea     rax, [rdx + 8*rdx]
        lea     rax, [rdx + 2*rax]
        imul    r10, rdx, 38
        lea     rcx, [rdx + rdx]
        mov     qword ptr [rsp - 112], rcx
        mov     r8, qword ptr [rsi + 24]
        lea     rcx, [r8 + 8*r8]
        lea     rcx, [r8 + 2*rcx]
        imul    r11, r8, 38
        mul     rdx
        mov     qword ptr [rsp - 32], rax
        mov     qword ptr [rsp - 24], rdx
        mov     r9, qword ptr [rsi + 16]
        mov     rax, r8
        mul     r10
        mov     qword ptr [rsp - 8], rdx
        mov     qword ptr [rsp - 40], rax
        mov     rax, rcx
        mul     r8
        mov     qword ptr [rsp], rdx
        mov     qword ptr [rsp - 16], rax
        mov     rax, r9
        mul     r10
        mov     rbx, rax
        mov     rcx, rdx
        add     r8, r8
        mov     qword ptr [rsp - 128], r8
        mov     rax, r9
        mul     r11
        mov     qword ptr [rsp - 72], rax
        mov     qword ptr [rsp - 64], rdx
        lea     r14, [r9 + r9]
        mov     qword ptr [rsp - 120], r14
        mov     rax, r9
        mul     r9
        mov     qword ptr [rsp - 56], rax
        mov     qword ptr [rsp - 48], rdx
        mov     rbp, qword ptr [rsi + 8]
        mov     rax, rbp
        mul     r10
        mov     r15, rdx
        mov     r9, rax
        mov     rax, rbp
        mul     r8
        mov     r11, rdx
        mov     r13, rax
        mov     rax, rbp
        mul     r14
        mov     r14, rax
        mov     r8, rdx
        mov     rsi, qword ptr [rsi]
        mov     rax, rbp
        mul     rbp
        mov     r10, rdx
        mov     r12, rax
        mov     rax, rsi
        mul     qword ptr [rsp - 112]
        mov     qword ptr [rsp - 80], rdx
        mov     qword ptr [rsp - 104], rax
        mov     rax, rsi
        mul     qword ptr [rsp - 128]
        mov     qword ptr [rsp - 88], rax
        mov     qword ptr [rsp - 128], rdx
        add     rbp, rbp
        mov     rax, rsi
        mul     qword ptr [rsp - 120]
        mov     qword ptr [rsp - 112], rdx
        mov     qword ptr [rsp - 96], rax
        mov     rax, rsi
        mul     rbp
        mov     rbp, rdx
        mov     qword ptr [rsp - 120], rax
        mov     rax, rsi
        mul     rsi
        add     r9, qword ptr [rsp - 72]
        adc     r15, qword ptr [rsp - 64]
        add     r9, rax
        adc     r15, rdx
        shld    r15, r9, 13
        movabs  rax, 2251799813685247
        and     r9, rax
        add     r13, qword ptr [rsp - 56]
        adc     r11, qword ptr [rsp - 48]
        add     r13, qword ptr [rsp - 104]
        adc     r11, qword ptr [rsp - 80]
        add     r14, qword ptr [rsp - 32]
        adc     r8, qword ptr [rsp - 24]
        add     r14, qword ptr [rsp - 88]
        adc     r8, qword ptr [rsp - 128]
        add     r12, qword ptr [rsp - 40]
        adc     r10, qword ptr [rsp - 8]
        add     r12, qword ptr [rsp - 96]
        adc     r10, qword ptr [rsp - 112]
        add     rbx, qword ptr [rsp - 16]
        adc     rcx, qword ptr [rsp]
        add     rbx, qword ptr [rsp - 120]
        adc     rcx, rbp
        add     rbx, r15
        adc     rcx, 0
        shld    rcx, rbx, 13
        and     rbx, rax
        add     rcx, r12
        adc     r10, 0
        shld    r10, rcx, 13
        and     rcx, rax
        add     r10, r14
        adc     r8, 0
        shld    r8, r10, 13
        and     r10, rax
        add     r8, r13
        adc     r11, 0
        shld    r11, r8, 13
        lea     rdx, [r11 + 8*r11]
        lea     rdx, [r11 + 2*rdx]
        add     rdx, r9
        mov     rsi, rdx
        shr     rsi, 51
        add     rsi, rbx
        mov     r9, rsi
        shr     r9, 51
        add     r9, rcx
        and     r8, rax
        and     rdx, rax
        and     rsi, rax
        mov     qword ptr [rdi], rdx
        mov     qword ptr [rdi + 8], rsi
        mov     qword ptr [rdi + 16], r9
        mov     qword ptr [rdi + 24], r10
        mov     qword ptr [rdi + 32], r8
        add     rsp, 8
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret

_Z29fiat_25519_carry_scmul_121666PmPKm:
        push    r15
        push    r14
        push    r12
        push    rbx
        mov     eax, 121666
        mul     qword ptr [rsi + 32]
        mov     r8, rdx
        mov     r10, rax
        mov     eax, 121666
        mul     qword ptr [rsi + 24]
        mov     rcx, rdx
        mov     r11, rax
        mov     eax, 121666
        mul     qword ptr [rsi + 16]
        mov     r14, rdx
        mov     rbx, rax
        mov     eax, 121666
        mul     qword ptr [rsi + 8]
        mov     r15, rax
        mov     r9, rdx
        mov     eax, 121666
        mul     qword ptr [rsi]
        shld    rdx, rax, 13
        movabs  rsi, 2251799813685247
        lea     r12, [rsi - 1]
        and     r12, rax
        add     rdx, r15
        adc     r9, 0
        shld    r9, rdx, 13
        and     rdx, rsi
        add     r9, rbx
        adc     r14, 0
        shld    r14, r9, 13
        and     r9, rsi
        add     r14, r11
        adc     rcx, 0
        shld    rcx, r14, 13
        and     r14, rsi
        add     rcx, r10
        adc     r8, 0
        shld    r8, rcx, 13
        and     rcx, rsi
        lea     rax, [r8 + 8*r8]
        lea     rax, [r8 + 2*rax]
        add     rax, r12
        mov     r8, rax
        shr     r8, 51
        and     rax, rsi
        movzx   r8d, r8b
        add     r8, rdx
        mov     rdx, r8
        shr     rdx, 51
        add     rdx, r9
        and     r8, rsi
        mov     qword ptr [rdi], rax
        mov     qword ptr [rdi + 8], r8
        mov     qword ptr [rdi + 16], rdx
        mov     qword ptr [rdi + 24], r14
        mov     qword ptr [rdi + 32], rcx
        pop     rbx
        pop     r12
        pop     r14
        pop     r15
        ret

_Z16fiat_25519_carryPmPKm:
        mov     r9, qword ptr [rsi]
        mov     rcx, r9
        shr     rcx, 51
        add     rcx, qword ptr [rsi + 8]
        mov     rax, rcx
        shr     rax, 51
        add     rax, qword ptr [rsi + 16]
        mov     rdx, rax
        shr     rdx, 51
        add     rdx, qword ptr [rsi + 24]
        mov     r8, rdx
        shr     r8, 51
        add     r8, qword ptr [rsi + 32]
        movabs  rsi, 2251799813685247
        and     r9, rsi
        mov     r10, r8
        shr     r10, 51
        lea     r11, [r10 + 8*r10]
        lea     r10, [r10 + 2*r11]
        add     r10, r9
        mov     r9, r10
        shr     r9, 51
        and     rcx, rsi
        add     rcx, r9
        and     r10, rsi
        mov     r9, rcx
        and     r9, rsi
        shr     rcx, 51
        and     rax, rsi
        add     rax, rcx
        and     rdx, rsi
        and     r8, rsi
        mov     qword ptr [rdi], r10
        mov     qword ptr [rdi + 8], r9
        mov     qword ptr [rdi + 16], rax
        mov     qword ptr [rdi + 24], rdx
        mov     qword ptr [rdi + 32], r8
        ret

_Z14fiat_25519_addPmPKmS1_:
        mov     rax, qword ptr [rdx]
        mov     rcx, qword ptr [rdx + 8]
        add     rax, qword ptr [rsi]
        add     rcx, qword ptr [rsi + 8]
        mov     r8, qword ptr [rdx + 16]
        add     r8, qword ptr [rsi + 16]
        mov     r9, qword ptr [rdx + 24]
        add     r9, qword ptr [rsi + 24]
        mov     rdx, qword ptr [rdx + 32]
        add     rdx, qword ptr [rsi + 32]
        mov     qword ptr [rdi], rax
        mov     qword ptr [rdi + 8], rcx
        mov     qword ptr [rdi + 16], r8
        mov     qword ptr [rdi + 24], r9
        mov     qword ptr [rdi + 32], rdx
        ret

_Z14fiat_25519_subPmPKmS1_:
        movabs  rax, 4503599627370494
        mov     rcx, qword ptr [rsi]
        add     rcx, rax
        sub     rcx, qword ptr [rdx]
        mov     r8, qword ptr [rsi + 8]
        add     r8, rax
        sub     r8, qword ptr [rdx + 8]
        mov     r9, qword ptr [rsi + 16]
        add     r9, rax
        sub     r9, qword ptr [rdx + 16]
        mov     r10, qword ptr [rsi + 24]
        add     r10, rax
        sub     r10, qword ptr [rdx + 24]
        add     rax, qword ptr [rsi + 32]
        add     rcx, -36
        sub     rax, qword ptr [rdx + 32]
        mov     qword ptr [rdi], rcx
        mov     qword ptr [rdi + 8], r8
        mov     qword ptr [rdi + 16], r9
        mov     qword ptr [rdi + 24], r10
        mov     qword ptr [rdi + 32], rax
        ret

_Z14fiat_25519_oppPmPKm:
        movabs  rax, 4503599627370494
        mov     rcx, rax
        sub     rcx, qword ptr [rsi]
        mov     rdx, rax
        sub     rdx, qword ptr [rsi + 8]
        mov     r8, rax
        sub     r8, qword ptr [rsi + 16]
        mov     r9, rax
        sub     r9, qword ptr [rsi + 24]
        add     rcx, -36
        sub     rax, qword ptr [rsi + 32]
        mov     qword ptr [rdi], rcx
        mov     qword ptr [rdi + 8], rdx
        mov     qword ptr [rdi + 16], r8
        mov     qword ptr [rdi + 24], r9
        mov     qword ptr [rdi + 32], rax
        ret

_Z20fiat_25519_selectznzPmhPKmS1_:
        push    r15
        push    r14
        push    rbx
        lea     rax, [rdx + 8]
        lea     r8, [rcx + 8]
        lea     r9, [rdx + 16]
        lea     r10, [rcx + 16]
        lea     r11, [rdx + 24]
        lea     rbx, [rcx + 24]
        lea     r14, [rdx + 32]
        lea     r15, [rcx + 32]
        test    esi, esi
        cmove   rcx, rdx
        cmove   r8, rax
        mov     rax, qword ptr [rcx]
        mov     rcx, qword ptr [r8]
        cmove   r10, r9
        mov     rdx, qword ptr [r10]
        cmove   rbx, r11
        mov     rsi, qword ptr [rbx]
        cmove   r15, r14
        mov     r8, qword ptr [r15]
        mov     qword ptr [rdi], rax
        mov     qword ptr [rdi + 8], rcx
        mov     qword ptr [rdi + 16], rdx
        mov     qword ptr [rdi + 24], rsi
        mov     qword ptr [rdi + 32], r8
        pop     rbx
        pop     r14
        pop     r15
        ret

_Z19fiat_25519_to_bytesPhPKm:
        push    rbp
        push    r15
        push    r14
        push    r13
        push    r12
        push    rbx
        mov     rax, qword ptr [rsi]
        movabs  r9, -2251799813685247
        add     rax, r9
        add     rax, 18
        movabs  r11, 2251799813685247
        mov     r10, rax
        and     r10, r11
        shr     rax, 51
        neg     eax
        movzx   eax, al
        mov     rcx, qword ptr [rsi + 8]
        add     rcx, r9
        sub     rcx, rax
        mov     rax, rcx
        and     rax, r11
        shr     rcx, 51
        neg     ecx
        movzx   ecx, cl
        mov     rdx, qword ptr [rsi + 16]
        add     rdx, r9
        sub     rdx, rcx
        mov     r8, rdx
        and     r8, r11
        shr     rdx, 51
        neg     edx
        movzx   ecx, dl
        mov     rbx, qword ptr [rsi + 24]
        add     rbx, r9
        sub     rbx, rcx
        mov     rdx, rbx
        and     rdx, r11
        shr     rbx, 51
        neg     ebx
        add     r9, qword ptr [rsi + 32]
        movzx   ecx, bl
        sub     r9, rcx
        movabs  rcx, 574208952489738240
        and     rcx, r9
        lea     rbx, [r11 - 18]
        test    rcx, rcx
        cmove   rbx, rcx
        cmovne  rcx, r11
        add     rbx, r10
        mov     r10, rbx
        mov     rsi, rbx
        shr     rsi, 51
        add     rax, rcx
        add     rax, rsi
        mov     rsi, rax
        shr     rsi, 51
        add     r8, rcx
        add     r8, rsi
        mov     rsi, r8
        shr     rsi, 51
        add     rdx, rcx
        add     rdx, rsi
        mov     rsi, rdx
        shr     rsi, 51
        add     rcx, r9
        add     rcx, rsi
        mov     ebp, ecx
        shl     ebp, 4
        mov     esi, r8d
        shl     esi, 6
        shr     r10, 48
        and     r10d, 7
        lea     r9d, [r10 + 8*rax]
        mov     dword ptr [rsp - 20], r9d
        mov     dword ptr [rsp - 24], eax
        mov     dword ptr [rsp - 28], eax
        mov     dword ptr [rsp - 32], eax
        mov     qword ptr [rsp - 8], rax
        mov     qword ptr [rsp - 16], rax
        shr     rax, 45
        and     eax, 63
        or      eax, esi
        mov     dword ptr [rsp - 36], r8d
        mov     dword ptr [rsp - 40], r8d
        mov     r13d, r8d
        mov     r12, r8
        mov     r15, r8
        mov     r14, r8
        shr     r8, 50
        and     r8d, 1
        lea     esi, [r8 + 2*rdx]
        mov     dword ptr [rsp - 44], esi
        mov     r11d, edx
        mov     r10d, edx
        mov     r9d, edx
        mov     r8, rdx
        mov     rsi, rdx
        shr     rdx, 47
        and     edx, 15
        or      edx, ebp
        mov     byte ptr [rdi], bl
        mov     byte ptr [rdi + 1], bh
        mov     ebp, ebx
        shr     ebp, 16
        mov     byte ptr [rdi + 2], bpl
        mov     ebp, ebx
        shr     ebp, 24
        mov     byte ptr [rdi + 3], bpl
        mov     rbp, rbx
        shr     rbp, 32
        mov     byte ptr [rdi + 4], bpl
        shr     rbx, 40
        mov     byte ptr [rdi + 5], bl
        mov     ebx, dword ptr [rsp - 20]
        mov     byte ptr [rdi + 6], bl
        mov     ebx, dword ptr [rsp - 24]
        shr     ebx, 5
        mov     byte ptr [rdi + 7], bl
        mov     ebx, dword ptr [rsp - 28]
        shr     ebx, 13
        mov     byte ptr [rdi + 8], bl
        mov     ebx, dword ptr [rsp - 32]
        shr     ebx, 21
        mov     byte ptr [rdi + 9], bl
        mov     rbx, qword ptr [rsp - 8]
        shr     rbx, 29
        mov     byte ptr [rdi + 10], bl
        mov     rbx, qword ptr [rsp - 16]
        shr     rbx, 37
        mov     byte ptr [rdi + 11], bl
        mov     byte ptr [rdi + 12], al
        mov     eax, dword ptr [rsp - 36]
        shr     eax, 2
        mov     byte ptr [rdi + 13], al
        mov     eax, dword ptr [rsp - 40]
        shr     eax, 10
        mov     byte ptr [rdi + 14], al
        shr     r13d, 18
        mov     byte ptr [rdi + 15], r13b
        shr     r12, 26
        mov     byte ptr [rdi + 16], r12b
        shr     r15, 34
        mov     byte ptr [rdi + 17], r15b
        shr     r14, 42
        mov     byte ptr [rdi + 18], r14b
        mov     eax, dword ptr [rsp - 44]
        mov     byte ptr [rdi + 19], al
        shr     r11d, 7
        mov     byte ptr [rdi + 20], r11b
        shr     r10d, 15
        mov     byte ptr [rdi + 21], r10b
        shr     r9d, 23
        mov     byte ptr [rdi + 22], r9b
        shr     r8, 31
        mov     byte ptr [rdi + 23], r8b
        shr     rsi, 39
        mov     byte ptr [rdi + 24], sil
        mov     byte ptr [rdi + 25], dl
        mov     eax, ecx
        shr     eax, 4
        mov     byte ptr [rdi + 26], al
        mov     eax, ecx
        shr     eax, 12
        mov     byte ptr [rdi + 27], al
        mov     eax, ecx
        shr     eax, 20
        mov     byte ptr [rdi + 28], al
        mov     rax, rcx
        shr     rax, 28
        mov     byte ptr [rdi + 29], al
        mov     rax, rcx
        shr     rax, 36
        mov     byte ptr [rdi + 30], al
        shr     rcx, 44
        and     cl, 127
        mov     byte ptr [rdi + 31], cl
        pop     rbx
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        pop     rbp
        ret

_Z21fiat_25519_from_bytesPmPKh:
        push    r14
        push    rbx
        movzx   eax, byte ptr [rsi + 31]
        shl     rax, 44
        movzx   ecx, byte ptr [rsi + 30]
        shl     rcx, 36
        or      rcx, rax
        movzx   eax, byte ptr [rsi + 29]
        shl     rax, 28
        or      rax, rcx
        movzx   ecx, byte ptr [rsi + 28]
        shl     ecx, 20
        or      rcx, rax
        movzx   edx, byte ptr [rsi + 27]
        shl     edx, 12
        or      rdx, rcx
        movzx   eax, byte ptr [rsi + 26]
        shl     eax, 4
        or      rax, rdx
        movzx   ecx, byte ptr [rsi + 25]
        shl     rcx, 47
        movzx   edx, byte ptr [rsi + 24]
        shl     rdx, 39
        or      rdx, rcx
        movzx   ecx, byte ptr [rsi + 23]
        shl     rcx, 31
        or      rcx, rdx
        movzx   edx, byte ptr [rsi + 22]
        shl     edx, 23
        or      rdx, rcx
        movzx   r8d, byte ptr [rsi + 21]
        shl     r8d, 15
        or      r8, rdx
        movzx   ecx, byte ptr [rsi + 20]
        shl     ecx, 7
        or      rcx, r8
        movzx   edx, byte ptr [rsi + 19]
        shl     rdx, 50
        movzx   r8d, byte ptr [rsi + 18]
        shl     r8, 42
        or      r8, rdx
        movzx   edx, byte ptr [rsi + 17]
        shl     rdx, 34
        or      rdx, r8
        movzx   r8d, byte ptr [rsi + 16]
        shl     r8, 26
        or      r8, rdx
        movzx   r9d, byte ptr [rsi + 15]
        shl     r9d, 18
        or      r9, r8
        movzx   edx, byte ptr [rsi + 14]
        shl     edx, 10
        or      rdx, r9
        movzx   r8d, byte ptr [rsi + 13]
        movzx   r9d, byte ptr [rsi + 12]
        shl     r9, 45
        movzx   r10d, byte ptr [rsi + 11]
        shl     r10, 37
        or      r10, r9
        movzx   r9d, byte ptr [rsi + 10]
        shl     r9, 29
        or      r9, r10
        movzx   r10d, byte ptr [rsi + 9]
        shl     r10d, 21
        or      r10, r9
        movzx   r11d, byte ptr [rsi + 8]
        shl     r11d, 13
        or      r11, r10
        movzx   r9d, byte ptr [rsi + 7]
        shl     r9d, 5
        or      r9, r11
        movzx   r10d, byte ptr [rsi + 6]
        shl     r10, 48
        movzx   r11d, byte ptr [rsi + 5]
        shl     r11, 40
        movzx   ebx, byte ptr [rsi + 4]
        shl     rbx, 32
        or      rbx, r11
        movzx   r11d, byte ptr [rsi + 3]
        shl     r11d, 24
        or      r11, rbx
        movzx   ebx, byte ptr [rsi + 2]
        shl     ebx, 16
        or      rbx, r11
        movzx   r11d, byte ptr [rsi + 1]
        shl     r11d, 8
        movzx   r14d, byte ptr [rsi]
        or      r14, rbx
        or      r14, r11
        add     r14, r10
        movabs  rsi, 2251799813685247
        mov     r10, r14
        and     r10, rsi
        shr     r14, 51
        movzx   r11d, r14b
        add     r11, r9
        mov     r9, r11
        and     r9, rsi
        shr     r11, 51
        movzx   r11d, r11b
        lea     rdx, [rdx + 4*r8]
        add     rdx, r11
        mov     r8, rdx
        and     r8, rsi
        shr     rdx, 51
        movzx   edx, dl
        add     rdx, rcx
        and     rsi, rdx
        shr     rdx, 51
        movzx   ecx, dl
        add     rcx, rax
        mov     qword ptr [rdi], r10
        mov     qword ptr [rdi + 8], r9
        mov     qword ptr [rdi + 16], r8
        mov     qword ptr [rdi + 24], rsi
        mov     qword ptr [rdi + 32], rcx
        pop     rbx
        pop     r14
        ret