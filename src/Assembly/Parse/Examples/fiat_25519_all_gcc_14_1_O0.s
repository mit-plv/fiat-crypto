_Z24fiat_25519_addcarryx_u51PmPhhmm:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-40], rdi
        mov     QWORD PTR [rbp-48], rsi
        mov     eax, edx
        mov     QWORD PTR [rbp-64], rcx
        mov     QWORD PTR [rbp-72], r8
        mov     BYTE PTR [rbp-52], al
        movzx   edx, BYTE PTR [rbp-52]
        mov     rax, QWORD PTR [rbp-64]
        add     rdx, rax
        mov     rax, QWORD PTR [rbp-72]
        add     rax, rdx
        mov     QWORD PTR [rbp-8], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-8]
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-8]
        shr     rax, 51
        mov     BYTE PTR [rbp-17], al
        mov     rax, QWORD PTR [rbp-40]
        mov     rdx, QWORD PTR [rbp-16]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-48]
        movzx   edx, BYTE PTR [rbp-17]
        mov     BYTE PTR [rax], dl
        nop
        pop     rbp
        ret
_Z25fiat_25519_subborrowx_u51PmPhhmm:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-40], rdi
        mov     QWORD PTR [rbp-48], rsi
        mov     eax, edx
        mov     QWORD PTR [rbp-64], rcx
        mov     QWORD PTR [rbp-72], r8
        mov     BYTE PTR [rbp-52], al
        movzx   eax, BYTE PTR [rbp-52]
        mov     rdx, QWORD PTR [rbp-64]
        sub     rdx, rax
        mov     rax, QWORD PTR [rbp-72]
        sub     rdx, rax
        mov     QWORD PTR [rbp-8], rdx
        mov     rax, QWORD PTR [rbp-8]
        sar     rax, 51
        mov     BYTE PTR [rbp-9], al
        mov     rax, QWORD PTR [rbp-8]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-40]
        mov     rdx, QWORD PTR [rbp-24]
        mov     QWORD PTR [rax], rdx
        movzx   eax, BYTE PTR [rbp-9]
        neg     eax
        mov     edx, eax
        mov     rax, QWORD PTR [rbp-48]
        mov     BYTE PTR [rax], dl
        nop
        pop     rbp
        ret
_Z22fiat_25519_cmovznz_u64Pmhmm:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-40], rdi
        mov     eax, esi
        mov     QWORD PTR [rbp-56], rdx
        mov     QWORD PTR [rbp-64], rcx
        mov     BYTE PTR [rbp-44], al
        cmp     BYTE PTR [rbp-44], 0
        setne   al
        mov     BYTE PTR [rbp-1], al
        movzx   eax, BYTE PTR [rbp-1]
        neg     eax
        movsx   rax, al
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-16]
        and     rax, QWORD PTR [rbp-64]
        mov     rdx, rax
        mov     rax, QWORD PTR [rbp-16]
        not     rax
        and     rax, QWORD PTR [rbp-56]
        or      rax, rdx
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-40]
        mov     rdx, QWORD PTR [rbp-24]
        mov     QWORD PTR [rax], rdx
        nop
        pop     rbp
        ret
_Z20fiat_25519_carry_mulPmPKmS1_:
        push    rbp
        mov     rbp, rsp
        push    rbx
        sub     rsp, 608
        mov     QWORD PTR [rbp-712], rdi
        mov     QWORD PTR [rbp-720], rsi
        mov     QWORD PTR [rbp-728], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-32], rax
        mov     QWORD PTR [rbp-24], rdx
        mov     QWORD PTR [rbp-32], rax
        mov     QWORD PTR [rbp-24], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-48], rax
        mov     QWORD PTR [rbp-40], rdx
        mov     QWORD PTR [rbp-48], rax
        mov     QWORD PTR [rbp-40], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 16
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-64], rax
        mov     QWORD PTR [rbp-56], rdx
        mov     QWORD PTR [rbp-64], rax
        mov     QWORD PTR [rbp-56], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 8
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-80], rax
        mov     QWORD PTR [rbp-72], rdx
        mov     QWORD PTR [rbp-80], rax
        mov     QWORD PTR [rbp-72], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-96], rax
        mov     QWORD PTR [rbp-88], rdx
        mov     QWORD PTR [rbp-96], rax
        mov     QWORD PTR [rbp-88], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-112], rax
        mov     QWORD PTR [rbp-104], rdx
        mov     QWORD PTR [rbp-112], rax
        mov     QWORD PTR [rbp-104], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 16
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-128], rax
        mov     QWORD PTR [rbp-120], rdx
        mov     QWORD PTR [rbp-128], rax
        mov     QWORD PTR [rbp-120], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-144], rax
        mov     QWORD PTR [rbp-136], rdx
        mov     QWORD PTR [rbp-144], rax
        mov     QWORD PTR [rbp-136], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-160], rax
        mov     QWORD PTR [rbp-152], rdx
        mov     QWORD PTR [rbp-160], rax
        mov     QWORD PTR [rbp-152], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rsi, rax
        mov     edi, 0
        mov     rax, QWORD PTR [rbp-728]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     rcx, rax
        mov     ebx, 0
        mov     rdx, rdi
        imul    rdx, rcx
        mov     rax, rbx
        imul    rax, rsi
        lea     r8, [rdx+rax]
        mov     rax, rsi
        mul     rcx
        lea     rcx, [r8+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-176], rax
        mov     QWORD PTR [rbp-168], rdx
        mov     QWORD PTR [rbp-176], rax
        mov     QWORD PTR [rbp-168], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-192], rax
        mov     QWORD PTR [rbp-184], rdx
        mov     QWORD PTR [rbp-192], rax
        mov     QWORD PTR [rbp-184], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 8
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-208], rax
        mov     QWORD PTR [rbp-200], rdx
        mov     QWORD PTR [rbp-208], rax
        mov     QWORD PTR [rbp-200], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-224], rax
        mov     QWORD PTR [rbp-216], rdx
        mov     QWORD PTR [rbp-224], rax
        mov     QWORD PTR [rbp-216], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 16
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-240], rax
        mov     QWORD PTR [rbp-232], rdx
        mov     QWORD PTR [rbp-240], rax
        mov     QWORD PTR [rbp-232], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 8
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-256], rax
        mov     QWORD PTR [rbp-248], rdx
        mov     QWORD PTR [rbp-256], rax
        mov     QWORD PTR [rbp-248], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-272], rax
        mov     QWORD PTR [rbp-264], rdx
        mov     QWORD PTR [rbp-272], rax
        mov     QWORD PTR [rbp-264], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 24
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-288], rax
        mov     QWORD PTR [rbp-280], rdx
        mov     QWORD PTR [rbp-288], rax
        mov     QWORD PTR [rbp-280], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 16
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-304], rax
        mov     QWORD PTR [rbp-296], rdx
        mov     QWORD PTR [rbp-304], rax
        mov     QWORD PTR [rbp-296], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 8
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-320], rax
        mov     QWORD PTR [rbp-312], rdx
        mov     QWORD PTR [rbp-320], rax
        mov     QWORD PTR [rbp-312], rdx
        mov     rax, QWORD PTR [rbp-720]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-336], rax
        mov     QWORD PTR [rbp-328], rdx
        mov     QWORD PTR [rbp-336], rax
        mov     QWORD PTR [rbp-328], rdx
        mov     rax, QWORD PTR [rbp-720]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 32
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-352], rax
        mov     QWORD PTR [rbp-344], rdx
        mov     QWORD PTR [rbp-352], rax
        mov     QWORD PTR [rbp-344], rdx
        mov     rax, QWORD PTR [rbp-720]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 24
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-368], rax
        mov     QWORD PTR [rbp-360], rdx
        mov     QWORD PTR [rbp-368], rax
        mov     QWORD PTR [rbp-360], rdx
        mov     rax, QWORD PTR [rbp-720]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 16
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-384], rax
        mov     QWORD PTR [rbp-376], rdx
        mov     QWORD PTR [rbp-384], rax
        mov     QWORD PTR [rbp-376], rdx
        mov     rax, QWORD PTR [rbp-720]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        add     rcx, 8
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-400], rax
        mov     QWORD PTR [rbp-392], rdx
        mov     QWORD PTR [rbp-400], rax
        mov     QWORD PTR [rbp-392], rdx
        mov     rax, QWORD PTR [rbp-720]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-728]
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-416], rax
        mov     QWORD PTR [rbp-408], rdx
        mov     QWORD PTR [rbp-416], rax
        mov     QWORD PTR [rbp-408], rdx
        mov     rcx, QWORD PTR [rbp-128]
        mov     rbx, QWORD PTR [rbp-120]
        mov     rax, QWORD PTR [rbp-80]
        mov     rdx, QWORD PTR [rbp-72]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-160]
        mov     rbx, QWORD PTR [rbp-152]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-176]
        mov     rbx, QWORD PTR [rbp-168]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-416]
        mov     rbx, QWORD PTR [rbp-408]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-432], rax
        mov     QWORD PTR [rbp-424], rdx
        mov     rax, QWORD PTR [rbp-432]
        mov     rdx, QWORD PTR [rbp-424]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-440], rax
        mov     rax, QWORD PTR [rbp-432]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-448], rax
        mov     rcx, QWORD PTR [rbp-208]
        mov     rbx, QWORD PTR [rbp-200]
        mov     rax, QWORD PTR [rbp-192]
        mov     rdx, QWORD PTR [rbp-184]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-240]
        mov     rbx, QWORD PTR [rbp-232]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-288]
        mov     rbx, QWORD PTR [rbp-280]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-352]
        mov     rbx, QWORD PTR [rbp-344]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-464], rax
        mov     QWORD PTR [rbp-456], rdx
        mov     rcx, QWORD PTR [rbp-224]
        mov     rbx, QWORD PTR [rbp-216]
        mov     rax, QWORD PTR [rbp-32]
        mov     rdx, QWORD PTR [rbp-24]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-256]
        mov     rbx, QWORD PTR [rbp-248]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-304]
        mov     rbx, QWORD PTR [rbp-296]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-368]
        mov     rbx, QWORD PTR [rbp-360]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-480], rax
        mov     QWORD PTR [rbp-472], rdx
        mov     rcx, QWORD PTR [rbp-96]
        mov     rbx, QWORD PTR [rbp-88]
        mov     rax, QWORD PTR [rbp-48]
        mov     rdx, QWORD PTR [rbp-40]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-272]
        mov     rbx, QWORD PTR [rbp-264]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-320]
        mov     rbx, QWORD PTR [rbp-312]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-384]
        mov     rbx, QWORD PTR [rbp-376]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-496], rax
        mov     QWORD PTR [rbp-488], rdx
        mov     rcx, QWORD PTR [rbp-112]
        mov     rbx, QWORD PTR [rbp-104]
        mov     rax, QWORD PTR [rbp-64]
        mov     rdx, QWORD PTR [rbp-56]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-144]
        mov     rbx, QWORD PTR [rbp-136]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-336]
        mov     rbx, QWORD PTR [rbp-328]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-400]
        mov     rbx, QWORD PTR [rbp-392]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-512], rax
        mov     QWORD PTR [rbp-504], rdx
        mov     rax, QWORD PTR [rbp-440]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-512]
        mov     rbx, QWORD PTR [rbp-504]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-528], rax
        mov     QWORD PTR [rbp-520], rdx
        mov     rax, QWORD PTR [rbp-528]
        mov     rdx, QWORD PTR [rbp-520]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-536], rax
        mov     rax, QWORD PTR [rbp-528]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-544], rax
        mov     rax, QWORD PTR [rbp-536]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-496]
        mov     rbx, QWORD PTR [rbp-488]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-560], rax
        mov     QWORD PTR [rbp-552], rdx
        mov     rax, QWORD PTR [rbp-560]
        mov     rdx, QWORD PTR [rbp-552]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-568], rax
        mov     rax, QWORD PTR [rbp-560]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-576], rax
        mov     rax, QWORD PTR [rbp-568]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-480]
        mov     rbx, QWORD PTR [rbp-472]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-592], rax
        mov     QWORD PTR [rbp-584], rdx
        mov     rax, QWORD PTR [rbp-592]
        mov     rdx, QWORD PTR [rbp-584]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-600], rax
        mov     rax, QWORD PTR [rbp-592]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-608], rax
        mov     rax, QWORD PTR [rbp-600]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-464]
        mov     rbx, QWORD PTR [rbp-456]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-624], rax
        mov     QWORD PTR [rbp-616], rdx
        mov     rax, QWORD PTR [rbp-624]
        mov     rdx, QWORD PTR [rbp-616]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-632], rax
        mov     rax, QWORD PTR [rbp-624]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-640], rax
        mov     rdx, QWORD PTR [rbp-632]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     QWORD PTR [rbp-648], rax
        mov     rdx, QWORD PTR [rbp-448]
        mov     rax, QWORD PTR [rbp-648]
        add     rax, rdx
        mov     QWORD PTR [rbp-656], rax
        mov     rax, QWORD PTR [rbp-656]
        shr     rax, 51
        mov     QWORD PTR [rbp-664], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-656]
        mov     QWORD PTR [rbp-672], rax
        mov     rdx, QWORD PTR [rbp-664]
        mov     rax, QWORD PTR [rbp-544]
        add     rax, rdx
        mov     QWORD PTR [rbp-680], rax
        mov     rax, QWORD PTR [rbp-680]
        shr     rax, 51
        mov     BYTE PTR [rbp-681], al
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-680]
        mov     QWORD PTR [rbp-696], rax
        movzx   edx, BYTE PTR [rbp-681]
        mov     rax, QWORD PTR [rbp-576]
        add     rax, rdx
        mov     QWORD PTR [rbp-704], rax
        mov     rax, QWORD PTR [rbp-712]
        mov     rdx, QWORD PTR [rbp-672]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-712]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-696]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-712]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-704]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-712]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-608]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-712]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-640]
        mov     QWORD PTR [rdx], rax
        nop
        mov     rbx, QWORD PTR [rbp-8]
        leave
        ret
_Z23fiat_25519_carry_squarePmPKm:
        push    rbp
        mov     rbp, rsp
        push    rbx
        sub     rsp, 496
        mov     QWORD PTR [rbp-616], rdi
        mov     QWORD PTR [rbp-624], rsi
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-24]
        add     rax, rax
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        add     rax, rax
        mov     QWORD PTR [rbp-40], rax
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     QWORD PTR [rbp-48], rax
        mov     rax, QWORD PTR [rbp-48]
        add     rax, rax
        mov     QWORD PTR [rbp-56], rax
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        add     rax, rax
        mov     QWORD PTR [rbp-64], rax
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        add     rax, rax
        mov     QWORD PTR [rbp-72], rax
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        add     rax, rax
        mov     QWORD PTR [rbp-80], rax
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-24]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-96], rax
        mov     QWORD PTR [rbp-88], rdx
        mov     QWORD PTR [rbp-96], rax
        mov     QWORD PTR [rbp-88], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-32]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-112], rax
        mov     QWORD PTR [rbp-104], rdx
        mov     QWORD PTR [rbp-112], rax
        mov     QWORD PTR [rbp-104], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-48]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-128], rax
        mov     QWORD PTR [rbp-120], rdx
        mov     QWORD PTR [rbp-128], rax
        mov     QWORD PTR [rbp-120], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-32]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-144], rax
        mov     QWORD PTR [rbp-136], rdx
        mov     QWORD PTR [rbp-144], rax
        mov     QWORD PTR [rbp-136], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-56]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-160], rax
        mov     QWORD PTR [rbp-152], rdx
        mov     QWORD PTR [rbp-160], rax
        mov     QWORD PTR [rbp-152], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-624]
        add     rcx, 16
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-176], rax
        mov     QWORD PTR [rbp-168], rdx
        mov     QWORD PTR [rbp-176], rax
        mov     QWORD PTR [rbp-168], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-32]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-192], rax
        mov     QWORD PTR [rbp-184], rdx
        mov     QWORD PTR [rbp-192], rax
        mov     QWORD PTR [rbp-184], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-64]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-208], rax
        mov     QWORD PTR [rbp-200], rdx
        mov     QWORD PTR [rbp-208], rax
        mov     QWORD PTR [rbp-200], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-72]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-224], rax
        mov     QWORD PTR [rbp-216], rdx
        mov     QWORD PTR [rbp-224], rax
        mov     QWORD PTR [rbp-216], rdx
        mov     rax, QWORD PTR [rbp-624]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-624]
        add     rcx, 8
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-240], rax
        mov     QWORD PTR [rbp-232], rdx
        mov     QWORD PTR [rbp-240], rax
        mov     QWORD PTR [rbp-232], rdx
        mov     rax, QWORD PTR [rbp-624]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-40]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-256], rax
        mov     QWORD PTR [rbp-248], rdx
        mov     QWORD PTR [rbp-256], rax
        mov     QWORD PTR [rbp-248], rdx
        mov     rax, QWORD PTR [rbp-624]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-64]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-272], rax
        mov     QWORD PTR [rbp-264], rdx
        mov     QWORD PTR [rbp-272], rax
        mov     QWORD PTR [rbp-264], rdx
        mov     rax, QWORD PTR [rbp-624]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-72]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-288], rax
        mov     QWORD PTR [rbp-280], rdx
        mov     QWORD PTR [rbp-288], rax
        mov     QWORD PTR [rbp-280], rdx
        mov     rax, QWORD PTR [rbp-624]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-80]
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-304], rax
        mov     QWORD PTR [rbp-296], rdx
        mov     QWORD PTR [rbp-304], rax
        mov     QWORD PTR [rbp-296], rdx
        mov     rax, QWORD PTR [rbp-624]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-624]
        mov     rcx, QWORD PTR [rcx]
        mov     rcx, rcx
        mov     ebx, 0
        mov     rdi, rdx
        imul    rdi, rcx
        mov     rsi, rbx
        imul    rsi, rax
        add     rsi, rdi
        mul     rcx
        lea     rcx, [rsi+rdx]
        mov     rdx, rcx
        mov     QWORD PTR [rbp-320], rax
        mov     QWORD PTR [rbp-312], rdx
        mov     QWORD PTR [rbp-320], rax
        mov     QWORD PTR [rbp-312], rdx
        mov     rcx, QWORD PTR [rbp-192]
        mov     rbx, QWORD PTR [rbp-184]
        mov     rax, QWORD PTR [rbp-160]
        mov     rdx, QWORD PTR [rbp-152]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-320]
        mov     rbx, QWORD PTR [rbp-312]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-336], rax
        mov     QWORD PTR [rbp-328], rdx
        mov     rax, QWORD PTR [rbp-336]
        mov     rdx, QWORD PTR [rbp-328]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-344], rax
        mov     rax, QWORD PTR [rbp-336]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-352], rax
        mov     rcx, QWORD PTR [rbp-208]
        mov     rbx, QWORD PTR [rbp-200]
        mov     rax, QWORD PTR [rbp-176]
        mov     rdx, QWORD PTR [rbp-168]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-256]
        mov     rbx, QWORD PTR [rbp-248]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-368], rax
        mov     QWORD PTR [rbp-360], rdx
        mov     rcx, QWORD PTR [rbp-224]
        mov     rbx, QWORD PTR [rbp-216]
        mov     rax, QWORD PTR [rbp-96]
        mov     rdx, QWORD PTR [rbp-88]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-272]
        mov     rbx, QWORD PTR [rbp-264]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-384], rax
        mov     QWORD PTR [rbp-376], rdx
        mov     rcx, QWORD PTR [rbp-240]
        mov     rbx, QWORD PTR [rbp-232]
        mov     rax, QWORD PTR [rbp-112]
        mov     rdx, QWORD PTR [rbp-104]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-288]
        mov     rbx, QWORD PTR [rbp-280]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-400], rax
        mov     QWORD PTR [rbp-392], rdx
        mov     rcx, QWORD PTR [rbp-144]
        mov     rbx, QWORD PTR [rbp-136]
        mov     rax, QWORD PTR [rbp-128]
        mov     rdx, QWORD PTR [rbp-120]
        add     rax, rcx
        adc     rdx, rbx
        mov     rcx, QWORD PTR [rbp-304]
        mov     rbx, QWORD PTR [rbp-296]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-416], rax
        mov     QWORD PTR [rbp-408], rdx
        mov     rax, QWORD PTR [rbp-344]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-416]
        mov     rbx, QWORD PTR [rbp-408]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-432], rax
        mov     QWORD PTR [rbp-424], rdx
        mov     rax, QWORD PTR [rbp-432]
        mov     rdx, QWORD PTR [rbp-424]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-440], rax
        mov     rax, QWORD PTR [rbp-432]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-448], rax
        mov     rax, QWORD PTR [rbp-440]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-400]
        mov     rbx, QWORD PTR [rbp-392]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-464], rax
        mov     QWORD PTR [rbp-456], rdx
        mov     rax, QWORD PTR [rbp-464]
        mov     rdx, QWORD PTR [rbp-456]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-472], rax
        mov     rax, QWORD PTR [rbp-464]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-480], rax
        mov     rax, QWORD PTR [rbp-472]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-384]
        mov     rbx, QWORD PTR [rbp-376]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-496], rax
        mov     QWORD PTR [rbp-488], rdx
        mov     rax, QWORD PTR [rbp-496]
        mov     rdx, QWORD PTR [rbp-488]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-504], rax
        mov     rax, QWORD PTR [rbp-496]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-512], rax
        mov     rax, QWORD PTR [rbp-504]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-368]
        mov     rbx, QWORD PTR [rbp-360]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-528], rax
        mov     QWORD PTR [rbp-520], rdx
        mov     rax, QWORD PTR [rbp-528]
        mov     rdx, QWORD PTR [rbp-520]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-536], rax
        mov     rax, QWORD PTR [rbp-528]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-544], rax
        mov     rdx, QWORD PTR [rbp-536]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     QWORD PTR [rbp-552], rax
        mov     rdx, QWORD PTR [rbp-352]
        mov     rax, QWORD PTR [rbp-552]
        add     rax, rdx
        mov     QWORD PTR [rbp-560], rax
        mov     rax, QWORD PTR [rbp-560]
        shr     rax, 51
        mov     QWORD PTR [rbp-568], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-560]
        mov     QWORD PTR [rbp-576], rax
        mov     rdx, QWORD PTR [rbp-568]
        mov     rax, QWORD PTR [rbp-448]
        add     rax, rdx
        mov     QWORD PTR [rbp-584], rax
        mov     rax, QWORD PTR [rbp-584]
        shr     rax, 51
        mov     BYTE PTR [rbp-585], al
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-584]
        mov     QWORD PTR [rbp-600], rax
        movzx   edx, BYTE PTR [rbp-585]
        mov     rax, QWORD PTR [rbp-480]
        add     rax, rdx
        mov     QWORD PTR [rbp-608], rax
        mov     rax, QWORD PTR [rbp-616]
        mov     rdx, QWORD PTR [rbp-576]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-616]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-600]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-616]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-608]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-616]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-512]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-616]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-544]
        mov     QWORD PTR [rdx], rax
        nop
        mov     rbx, QWORD PTR [rbp-8]
        leave
        ret
_Z29fiat_25519_carry_scmul_121666PmPKm:
        push    rbp
        mov     rbp, rsp
        push    rbx
        sub     rsp, 192
        mov     QWORD PTR [rbp-312], rdi
        mov     QWORD PTR [rbp-320], rsi
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        imul    rsi, rdx, 121666
        imul    rcx, rax, 0
        add     rcx, rsi
        mov     esi, 121666
        mul     rsi
        add     rcx, rdx
        mov     rdx, rcx
        mov     QWORD PTR [rbp-32], rax
        mov     QWORD PTR [rbp-24], rdx
        mov     QWORD PTR [rbp-32], rax
        mov     QWORD PTR [rbp-24], rdx
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        imul    rsi, rdx, 121666
        imul    rcx, rax, 0
        add     rcx, rsi
        mov     esi, 121666
        mul     rsi
        add     rcx, rdx
        mov     rdx, rcx
        mov     QWORD PTR [rbp-48], rax
        mov     QWORD PTR [rbp-40], rdx
        mov     QWORD PTR [rbp-48], rax
        mov     QWORD PTR [rbp-40], rdx
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        imul    rsi, rdx, 121666
        imul    rcx, rax, 0
        add     rcx, rsi
        mov     esi, 121666
        mul     rsi
        add     rcx, rdx
        mov     rdx, rcx
        mov     QWORD PTR [rbp-64], rax
        mov     QWORD PTR [rbp-56], rdx
        mov     QWORD PTR [rbp-64], rax
        mov     QWORD PTR [rbp-56], rdx
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        imul    rsi, rdx, 121666
        imul    rcx, rax, 0
        add     rcx, rsi
        mov     esi, 121666
        mul     rsi
        add     rcx, rdx
        mov     rdx, rcx
        mov     QWORD PTR [rbp-80], rax
        mov     QWORD PTR [rbp-72], rdx
        mov     QWORD PTR [rbp-80], rax
        mov     QWORD PTR [rbp-72], rdx
        mov     rax, QWORD PTR [rbp-320]
        mov     rax, QWORD PTR [rax]
        mov     rax, rax
        mov     edx, 0
        imul    rsi, rdx, 121666
        imul    rcx, rax, 0
        add     rcx, rsi
        mov     esi, 121666
        mul     rsi
        add     rcx, rdx
        mov     rdx, rcx
        mov     QWORD PTR [rbp-96], rax
        mov     QWORD PTR [rbp-88], rdx
        mov     QWORD PTR [rbp-96], rax
        mov     QWORD PTR [rbp-88], rdx
        mov     rax, QWORD PTR [rbp-96]
        mov     rdx, QWORD PTR [rbp-88]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-104], rax
        mov     rax, QWORD PTR [rbp-96]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-112], rax
        mov     rax, QWORD PTR [rbp-104]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-80]
        mov     rbx, QWORD PTR [rbp-72]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-128], rax
        mov     QWORD PTR [rbp-120], rdx
        mov     rax, QWORD PTR [rbp-128]
        mov     rdx, QWORD PTR [rbp-120]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-136], rax
        mov     rax, QWORD PTR [rbp-128]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-144], rax
        mov     rax, QWORD PTR [rbp-136]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-64]
        mov     rbx, QWORD PTR [rbp-56]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-160], rax
        mov     QWORD PTR [rbp-152], rdx
        mov     rax, QWORD PTR [rbp-160]
        mov     rdx, QWORD PTR [rbp-152]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-168], rax
        mov     rax, QWORD PTR [rbp-160]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-176], rax
        mov     rax, QWORD PTR [rbp-168]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-48]
        mov     rbx, QWORD PTR [rbp-40]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-192], rax
        mov     QWORD PTR [rbp-184], rdx
        mov     rax, QWORD PTR [rbp-192]
        mov     rdx, QWORD PTR [rbp-184]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-200], rax
        mov     rax, QWORD PTR [rbp-192]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-208], rax
        mov     rax, QWORD PTR [rbp-200]
        mov     edx, 0
        mov     rcx, QWORD PTR [rbp-32]
        mov     rbx, QWORD PTR [rbp-24]
        add     rax, rcx
        adc     rdx, rbx
        mov     QWORD PTR [rbp-224], rax
        mov     QWORD PTR [rbp-216], rdx
        mov     rax, QWORD PTR [rbp-224]
        mov     rdx, QWORD PTR [rbp-216]
        shrd    rax, rdx, 51
        shr     rdx, 51
        mov     QWORD PTR [rbp-232], rax
        mov     rax, QWORD PTR [rbp-224]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     QWORD PTR [rbp-240], rax
        mov     rdx, QWORD PTR [rbp-232]
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        mov     QWORD PTR [rbp-248], rax
        mov     rdx, QWORD PTR [rbp-112]
        mov     rax, QWORD PTR [rbp-248]
        add     rax, rdx
        mov     QWORD PTR [rbp-256], rax
        mov     rax, QWORD PTR [rbp-256]
        shr     rax, 51
        mov     BYTE PTR [rbp-257], al
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-256]
        mov     QWORD PTR [rbp-272], rax
        movzx   edx, BYTE PTR [rbp-257]
        mov     rax, QWORD PTR [rbp-144]
        add     rax, rdx
        mov     QWORD PTR [rbp-280], rax
        mov     rax, QWORD PTR [rbp-280]
        shr     rax, 51
        mov     BYTE PTR [rbp-281], al
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-280]
        mov     QWORD PTR [rbp-296], rax
        movzx   edx, BYTE PTR [rbp-281]
        mov     rax, QWORD PTR [rbp-176]
        add     rax, rdx
        mov     QWORD PTR [rbp-304], rax
        mov     rax, QWORD PTR [rbp-312]
        mov     rdx, QWORD PTR [rbp-272]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-312]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-296]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-312]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-304]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-312]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-208]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-312]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-240]
        mov     QWORD PTR [rdx], rax
        nop
        mov     rbx, QWORD PTR [rbp-8]
        leave
        ret
_Z16fiat_25519_carryPmPKm:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-104], rdi
        mov     QWORD PTR [rbp-112], rsi
        mov     rax, QWORD PTR [rbp-112]
        mov     rax, QWORD PTR [rax]
        mov     QWORD PTR [rbp-8], rax
        mov     rax, QWORD PTR [rbp-8]
        shr     rax, 51
        mov     rdx, rax
        mov     rax, QWORD PTR [rbp-112]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-16]
        shr     rax, 51
        mov     rdx, rax
        mov     rax, QWORD PTR [rbp-112]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-24]
        shr     rax, 51
        mov     rdx, rax
        mov     rax, QWORD PTR [rbp-112]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-32]
        shr     rax, 51
        mov     rdx, rax
        mov     rax, QWORD PTR [rbp-112]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-40], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-8]
        mov     rcx, rax
        mov     rax, QWORD PTR [rbp-40]
        shr     rax, 51
        mov     rdx, rax
        mov     rax, rdx
        sal     rax, 3
        add     rax, rdx
        add     rax, rax
        add     rax, rdx
        add     rax, rcx
        mov     QWORD PTR [rbp-48], rax
        mov     rax, QWORD PTR [rbp-48]
        shr     rax, 51
        movzx   edx, al
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-16]
        add     rax, rdx
        mov     QWORD PTR [rbp-56], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-48]
        mov     QWORD PTR [rbp-64], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-56]
        mov     QWORD PTR [rbp-72], rax
        mov     rax, QWORD PTR [rbp-56]
        shr     rax, 51
        movzx   edx, al
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-24]
        add     rax, rdx
        mov     QWORD PTR [rbp-80], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-32]
        mov     QWORD PTR [rbp-88], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-40]
        mov     QWORD PTR [rbp-96], rax
        mov     rax, QWORD PTR [rbp-104]
        mov     rdx, QWORD PTR [rbp-64]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-104]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-72]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-104]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-80]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-104]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-88]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-104]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-96]
        mov     QWORD PTR [rdx], rax
        nop
        pop     rbp
        ret
_Z14fiat_25519_addPmPKmS1_:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-56], rdi
        mov     QWORD PTR [rbp-64], rsi
        mov     QWORD PTR [rbp-72], rdx
        mov     rax, QWORD PTR [rbp-64]
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-8], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 8
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 16
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        add     rax, rdx
        mov     QWORD PTR [rbp-40], rax
        mov     rax, QWORD PTR [rbp-56]
        mov     rdx, QWORD PTR [rbp-8]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-16]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-24]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-32]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-40]
        mov     QWORD PTR [rdx], rax
        nop
        pop     rbp
        ret
_Z14fiat_25519_subPmPKmS1_:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-56], rdi
        mov     QWORD PTR [rbp-64], rsi
        mov     QWORD PTR [rbp-72], rdx
        mov     rax, QWORD PTR [rbp-64]
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        mov     rax, QWORD PTR [rax]
        sub     rdx, rax
        movabs  rax, 4503599627370458
        add     rax, rdx
        mov     QWORD PTR [rbp-8], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 8
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        sub     rdx, rax
        movabs  rax, 4503599627370494
        add     rax, rdx
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 16
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        sub     rdx, rax
        movabs  rax, 4503599627370494
        add     rax, rdx
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        sub     rdx, rax
        movabs  rax, 4503599627370494
        add     rax, rdx
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        sub     rdx, rax
        movabs  rax, 4503599627370494
        add     rax, rdx
        mov     QWORD PTR [rbp-40], rax
        mov     rax, QWORD PTR [rbp-56]
        mov     rdx, QWORD PTR [rbp-8]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-16]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-24]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-32]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-40]
        mov     QWORD PTR [rdx], rax
        nop
        pop     rbp
        ret
_Z14fiat_25519_oppPmPKm:
        push    rbp
        mov     rbp, rsp
        mov     QWORD PTR [rbp-56], rdi
        mov     QWORD PTR [rbp-64], rsi
        mov     rax, QWORD PTR [rbp-64]
        mov     rax, QWORD PTR [rax]
        movabs  rdx, 4503599627370458
        sub     rdx, rax
        mov     QWORD PTR [rbp-8], rdx
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 8
        mov     rax, QWORD PTR [rax]
        movabs  rdx, 4503599627370494
        sub     rdx, rax
        mov     QWORD PTR [rbp-16], rdx
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 16
        mov     rax, QWORD PTR [rax]
        movabs  rdx, 4503599627370494
        sub     rdx, rax
        mov     QWORD PTR [rbp-24], rdx
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 24
        mov     rax, QWORD PTR [rax]
        movabs  rdx, 4503599627370494
        sub     rdx, rax
        mov     QWORD PTR [rbp-32], rdx
        mov     rax, QWORD PTR [rbp-64]
        add     rax, 32
        mov     rax, QWORD PTR [rax]
        movabs  rdx, 4503599627370494
        sub     rdx, rax
        mov     QWORD PTR [rbp-40], rdx
        mov     rax, QWORD PTR [rbp-56]
        mov     rdx, QWORD PTR [rbp-8]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-16]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-24]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-32]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-40]
        mov     QWORD PTR [rdx], rax
        nop
        pop     rbp
        ret
_Z20fiat_25519_selectznzPmhPKmS1_:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 80
        mov     QWORD PTR [rbp-56], rdi
        mov     eax, esi
        mov     QWORD PTR [rbp-72], rdx
        mov     QWORD PTR [rbp-80], rcx
        mov     BYTE PTR [rbp-60], al
        mov     rax, QWORD PTR [rbp-80]
        mov     rcx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        mov     rdx, QWORD PTR [rax]
        movzx   esi, BYTE PTR [rbp-60]
        lea     rax, [rbp-8]
        mov     rdi, rax
        call    _Z22fiat_25519_cmovznz_u64Pmhmm
        mov     rax, QWORD PTR [rbp-80]
        add     rax, 8
        mov     rcx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 8
        mov     rdx, QWORD PTR [rax]
        movzx   esi, BYTE PTR [rbp-60]
        lea     rax, [rbp-16]
        mov     rdi, rax
        call    _Z22fiat_25519_cmovznz_u64Pmhmm
        mov     rax, QWORD PTR [rbp-80]
        add     rax, 16
        mov     rcx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 16
        mov     rdx, QWORD PTR [rax]
        movzx   esi, BYTE PTR [rbp-60]
        lea     rax, [rbp-24]
        mov     rdi, rax
        call    _Z22fiat_25519_cmovznz_u64Pmhmm
        mov     rax, QWORD PTR [rbp-80]
        add     rax, 24
        mov     rcx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 24
        mov     rdx, QWORD PTR [rax]
        movzx   esi, BYTE PTR [rbp-60]
        lea     rax, [rbp-32]
        mov     rdi, rax
        call    _Z22fiat_25519_cmovznz_u64Pmhmm
        mov     rax, QWORD PTR [rbp-80]
        add     rax, 32
        mov     rcx, QWORD PTR [rax]
        mov     rax, QWORD PTR [rbp-72]
        add     rax, 32
        mov     rdx, QWORD PTR [rax]
        movzx   esi, BYTE PTR [rbp-60]
        lea     rax, [rbp-40]
        mov     rdi, rax
        call    _Z22fiat_25519_cmovznz_u64Pmhmm
        mov     rdx, QWORD PTR [rbp-8]
        mov     rax, QWORD PTR [rbp-56]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-16]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-24]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-32]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-56]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-40]
        mov     QWORD PTR [rdx], rax
        nop
        leave
        ret
_Z19fiat_25519_to_bytesPhPKm:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 704
        mov     QWORD PTR [rbp-696], rdi
        mov     QWORD PTR [rbp-704], rsi
        mov     rax, QWORD PTR [rbp-704]
        mov     rdx, QWORD PTR [rax]
        lea     rsi, [rbp-529]
        lea     rax, [rbp-528]
        movabs  r8, 2251799813685229
        mov     rcx, rdx
        mov     edx, 0
        mov     rdi, rax
        call    _Z25fiat_25519_subborrowx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-704]
        add     rax, 8
        mov     rcx, QWORD PTR [rax]
        movzx   eax, BYTE PTR [rbp-529]
        movzx   edx, al
        lea     rsi, [rbp-545]
        lea     rax, [rbp-544]
        movabs  r8, 2251799813685247
        mov     rdi, rax
        call    _Z25fiat_25519_subborrowx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-704]
        add     rax, 16
        mov     rcx, QWORD PTR [rax]
        movzx   eax, BYTE PTR [rbp-545]
        movzx   edx, al
        lea     rsi, [rbp-561]
        lea     rax, [rbp-560]
        movabs  r8, 2251799813685247
        mov     rdi, rax
        call    _Z25fiat_25519_subborrowx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-704]
        add     rax, 24
        mov     rcx, QWORD PTR [rax]
        movzx   eax, BYTE PTR [rbp-561]
        movzx   edx, al
        lea     rsi, [rbp-577]
        lea     rax, [rbp-576]
        movabs  r8, 2251799813685247
        mov     rdi, rax
        call    _Z25fiat_25519_subborrowx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-704]
        add     rax, 32
        mov     rcx, QWORD PTR [rax]
        movzx   eax, BYTE PTR [rbp-577]
        movzx   edx, al
        lea     rsi, [rbp-593]
        lea     rax, [rbp-592]
        movabs  r8, 2251799813685247
        mov     rdi, rax
        call    _Z25fiat_25519_subborrowx_u51PmPhhmm
        movzx   eax, BYTE PTR [rbp-593]
        movzx   esi, al
        lea     rax, [rbp-608]
        mov     rcx, -1
        mov     edx, 0
        mov     rdi, rax
        call    _Z22fiat_25519_cmovznz_u64Pmhmm
        mov     rax, QWORD PTR [rbp-608]
        movabs  rdx, 2251799813685229
        and     rax, rdx
        mov     rcx, rax
        mov     rdx, QWORD PTR [rbp-528]
        lea     rsi, [rbp-617]
        lea     rax, [rbp-616]
        mov     r8, rcx
        mov     rcx, rdx
        mov     edx, 0
        mov     rdi, rax
        call    _Z24fiat_25519_addcarryx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-608]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     rdi, rax
        mov     rcx, QWORD PTR [rbp-544]
        movzx   eax, BYTE PTR [rbp-617]
        movzx   edx, al
        lea     rsi, [rbp-633]
        lea     rax, [rbp-632]
        mov     r8, rdi
        mov     rdi, rax
        call    _Z24fiat_25519_addcarryx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-608]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     rdi, rax
        mov     rcx, QWORD PTR [rbp-560]
        movzx   eax, BYTE PTR [rbp-633]
        movzx   edx, al
        lea     rsi, [rbp-649]
        lea     rax, [rbp-648]
        mov     r8, rdi
        mov     rdi, rax
        call    _Z24fiat_25519_addcarryx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-608]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     rdi, rax
        mov     rcx, QWORD PTR [rbp-576]
        movzx   eax, BYTE PTR [rbp-649]
        movzx   edx, al
        lea     rsi, [rbp-665]
        lea     rax, [rbp-664]
        mov     r8, rdi
        mov     rdi, rax
        call    _Z24fiat_25519_addcarryx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-608]
        movabs  rdx, 2251799813685247
        and     rax, rdx
        mov     rdi, rax
        mov     rcx, QWORD PTR [rbp-592]
        movzx   eax, BYTE PTR [rbp-665]
        movzx   edx, al
        lea     rsi, [rbp-681]
        lea     rax, [rbp-680]
        mov     r8, rdi
        mov     rdi, rax
        call    _Z24fiat_25519_addcarryx_u51PmPhhmm
        mov     rax, QWORD PTR [rbp-680]
        sal     rax, 4
        mov     QWORD PTR [rbp-8], rax
        mov     rax, QWORD PTR [rbp-664]
        add     rax, rax
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-648]
        sal     rax, 6
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-632]
        sal     rax, 3
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-616]
        mov     BYTE PTR [rbp-33], al
        mov     rax, QWORD PTR [rbp-616]
        shr     rax, 8
        mov     QWORD PTR [rbp-48], rax
        mov     rax, QWORD PTR [rbp-48]
        mov     BYTE PTR [rbp-49], al
        mov     rax, QWORD PTR [rbp-48]
        shr     rax, 8
        mov     QWORD PTR [rbp-64], rax
        mov     rax, QWORD PTR [rbp-64]
        mov     BYTE PTR [rbp-65], al
        mov     rax, QWORD PTR [rbp-64]
        shr     rax, 8
        mov     QWORD PTR [rbp-80], rax
        mov     rax, QWORD PTR [rbp-80]
        mov     BYTE PTR [rbp-81], al
        mov     rax, QWORD PTR [rbp-80]
        shr     rax, 8
        mov     QWORD PTR [rbp-96], rax
        mov     rax, QWORD PTR [rbp-96]
        mov     BYTE PTR [rbp-97], al
        mov     rax, QWORD PTR [rbp-96]
        shr     rax, 8
        mov     QWORD PTR [rbp-112], rax
        mov     rax, QWORD PTR [rbp-112]
        mov     BYTE PTR [rbp-113], al
        mov     rax, QWORD PTR [rbp-112]
        shr     rax, 8
        mov     BYTE PTR [rbp-114], al
        movzx   edx, BYTE PTR [rbp-114]
        mov     rax, QWORD PTR [rbp-32]
        add     rax, rdx
        mov     QWORD PTR [rbp-128], rax
        mov     rax, QWORD PTR [rbp-128]
        mov     BYTE PTR [rbp-129], al
        mov     rax, QWORD PTR [rbp-128]
        shr     rax, 8
        mov     QWORD PTR [rbp-144], rax
        mov     rax, QWORD PTR [rbp-144]
        mov     BYTE PTR [rbp-145], al
        mov     rax, QWORD PTR [rbp-144]
        shr     rax, 8
        mov     QWORD PTR [rbp-160], rax
        mov     rax, QWORD PTR [rbp-160]
        mov     BYTE PTR [rbp-161], al
        mov     rax, QWORD PTR [rbp-160]
        shr     rax, 8
        mov     QWORD PTR [rbp-176], rax
        mov     rax, QWORD PTR [rbp-176]
        mov     BYTE PTR [rbp-177], al
        mov     rax, QWORD PTR [rbp-176]
        shr     rax, 8
        mov     QWORD PTR [rbp-192], rax
        mov     rax, QWORD PTR [rbp-192]
        mov     BYTE PTR [rbp-193], al
        mov     rax, QWORD PTR [rbp-192]
        shr     rax, 8
        mov     QWORD PTR [rbp-208], rax
        mov     rax, QWORD PTR [rbp-208]
        mov     BYTE PTR [rbp-209], al
        mov     rax, QWORD PTR [rbp-208]
        shr     rax, 8
        mov     BYTE PTR [rbp-210], al
        movzx   edx, BYTE PTR [rbp-210]
        mov     rax, QWORD PTR [rbp-24]
        add     rax, rdx
        mov     QWORD PTR [rbp-224], rax
        mov     rax, QWORD PTR [rbp-224]
        mov     BYTE PTR [rbp-225], al
        mov     rax, QWORD PTR [rbp-224]
        shr     rax, 8
        mov     QWORD PTR [rbp-240], rax
        mov     rax, QWORD PTR [rbp-240]
        mov     BYTE PTR [rbp-241], al
        mov     rax, QWORD PTR [rbp-240]
        shr     rax, 8
        mov     QWORD PTR [rbp-256], rax
        mov     rax, QWORD PTR [rbp-256]
        mov     BYTE PTR [rbp-257], al
        mov     rax, QWORD PTR [rbp-256]
        shr     rax, 8
        mov     QWORD PTR [rbp-272], rax
        mov     rax, QWORD PTR [rbp-272]
        mov     BYTE PTR [rbp-273], al
        mov     rax, QWORD PTR [rbp-272]
        shr     rax, 8
        mov     QWORD PTR [rbp-288], rax
        mov     rax, QWORD PTR [rbp-288]
        mov     BYTE PTR [rbp-289], al
        mov     rax, QWORD PTR [rbp-288]
        shr     rax, 8
        mov     QWORD PTR [rbp-304], rax
        mov     rax, QWORD PTR [rbp-304]
        mov     BYTE PTR [rbp-305], al
        mov     rax, QWORD PTR [rbp-304]
        shr     rax, 8
        mov     QWORD PTR [rbp-320], rax
        mov     rax, QWORD PTR [rbp-320]
        mov     BYTE PTR [rbp-321], al
        mov     rax, QWORD PTR [rbp-320]
        shr     rax, 8
        mov     BYTE PTR [rbp-322], al
        movzx   edx, BYTE PTR [rbp-322]
        mov     rax, QWORD PTR [rbp-16]
        add     rax, rdx
        mov     QWORD PTR [rbp-336], rax
        mov     rax, QWORD PTR [rbp-336]
        mov     BYTE PTR [rbp-337], al
        mov     rax, QWORD PTR [rbp-336]
        shr     rax, 8
        mov     QWORD PTR [rbp-352], rax
        mov     rax, QWORD PTR [rbp-352]
        mov     BYTE PTR [rbp-353], al
        mov     rax, QWORD PTR [rbp-352]
        shr     rax, 8
        mov     QWORD PTR [rbp-368], rax
        mov     rax, QWORD PTR [rbp-368]
        mov     BYTE PTR [rbp-369], al
        mov     rax, QWORD PTR [rbp-368]
        shr     rax, 8
        mov     QWORD PTR [rbp-384], rax
        mov     rax, QWORD PTR [rbp-384]
        mov     BYTE PTR [rbp-385], al
        mov     rax, QWORD PTR [rbp-384]
        shr     rax, 8
        mov     QWORD PTR [rbp-400], rax
        mov     rax, QWORD PTR [rbp-400]
        mov     BYTE PTR [rbp-401], al
        mov     rax, QWORD PTR [rbp-400]
        shr     rax, 8
        mov     QWORD PTR [rbp-416], rax
        mov     rax, QWORD PTR [rbp-416]
        mov     BYTE PTR [rbp-417], al
        mov     rax, QWORD PTR [rbp-416]
        shr     rax, 8
        mov     BYTE PTR [rbp-418], al
        movzx   edx, BYTE PTR [rbp-418]
        mov     rax, QWORD PTR [rbp-8]
        add     rax, rdx
        mov     QWORD PTR [rbp-432], rax
        mov     rax, QWORD PTR [rbp-432]
        mov     BYTE PTR [rbp-433], al
        mov     rax, QWORD PTR [rbp-432]
        shr     rax, 8
        mov     QWORD PTR [rbp-448], rax
        mov     rax, QWORD PTR [rbp-448]
        mov     BYTE PTR [rbp-449], al
        mov     rax, QWORD PTR [rbp-448]
        shr     rax, 8
        mov     QWORD PTR [rbp-464], rax
        mov     rax, QWORD PTR [rbp-464]
        mov     BYTE PTR [rbp-465], al
        mov     rax, QWORD PTR [rbp-464]
        shr     rax, 8
        mov     QWORD PTR [rbp-480], rax
        mov     rax, QWORD PTR [rbp-480]
        mov     BYTE PTR [rbp-481], al
        mov     rax, QWORD PTR [rbp-480]
        shr     rax, 8
        mov     QWORD PTR [rbp-496], rax
        mov     rax, QWORD PTR [rbp-496]
        mov     BYTE PTR [rbp-497], al
        mov     rax, QWORD PTR [rbp-496]
        shr     rax, 8
        mov     QWORD PTR [rbp-512], rax
        mov     rax, QWORD PTR [rbp-512]
        mov     BYTE PTR [rbp-513], al
        mov     rax, QWORD PTR [rbp-512]
        shr     rax, 8
        mov     BYTE PTR [rbp-514], al
        mov     rax, QWORD PTR [rbp-696]
        movzx   edx, BYTE PTR [rbp-33]
        mov     BYTE PTR [rax], dl
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+1]
        movzx   eax, BYTE PTR [rbp-49]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+2]
        movzx   eax, BYTE PTR [rbp-65]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+3]
        movzx   eax, BYTE PTR [rbp-81]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+4]
        movzx   eax, BYTE PTR [rbp-97]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+5]
        movzx   eax, BYTE PTR [rbp-113]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+6]
        movzx   eax, BYTE PTR [rbp-129]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+7]
        movzx   eax, BYTE PTR [rbp-145]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+8]
        movzx   eax, BYTE PTR [rbp-161]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+9]
        movzx   eax, BYTE PTR [rbp-177]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+10]
        movzx   eax, BYTE PTR [rbp-193]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+11]
        movzx   eax, BYTE PTR [rbp-209]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+12]
        movzx   eax, BYTE PTR [rbp-225]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+13]
        movzx   eax, BYTE PTR [rbp-241]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+14]
        movzx   eax, BYTE PTR [rbp-257]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+15]
        movzx   eax, BYTE PTR [rbp-273]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+16]
        movzx   eax, BYTE PTR [rbp-289]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+17]
        movzx   eax, BYTE PTR [rbp-305]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+18]
        movzx   eax, BYTE PTR [rbp-321]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+19]
        movzx   eax, BYTE PTR [rbp-337]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+20]
        movzx   eax, BYTE PTR [rbp-353]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+21]
        movzx   eax, BYTE PTR [rbp-369]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+22]
        movzx   eax, BYTE PTR [rbp-385]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+23]
        movzx   eax, BYTE PTR [rbp-401]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+24]
        movzx   eax, BYTE PTR [rbp-417]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+25]
        movzx   eax, BYTE PTR [rbp-433]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+26]
        movzx   eax, BYTE PTR [rbp-449]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+27]
        movzx   eax, BYTE PTR [rbp-465]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+28]
        movzx   eax, BYTE PTR [rbp-481]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+29]
        movzx   eax, BYTE PTR [rbp-497]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+30]
        movzx   eax, BYTE PTR [rbp-513]
        mov     BYTE PTR [rdx], al
        mov     rax, QWORD PTR [rbp-696]
        lea     rdx, [rax+31]
        movzx   eax, BYTE PTR [rbp-514]
        mov     BYTE PTR [rdx], al
        nop
        leave
        ret
_Z21fiat_25519_from_bytesPmPKh:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 472
        mov     QWORD PTR [rbp-584], rdi
        mov     QWORD PTR [rbp-592], rsi
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 31
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 44
        mov     QWORD PTR [rbp-8], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 30
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 36
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 29
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 28
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 28
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 20
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 27
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 12
        mov     QWORD PTR [rbp-40], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 26
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 4
        mov     QWORD PTR [rbp-48], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 25
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 47
        mov     QWORD PTR [rbp-56], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 24
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 39
        mov     QWORD PTR [rbp-64], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 23
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 31
        mov     QWORD PTR [rbp-72], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 22
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 23
        mov     QWORD PTR [rbp-80], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 21
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 15
        mov     QWORD PTR [rbp-88], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 20
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 7
        mov     QWORD PTR [rbp-96], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 19
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 50
        mov     QWORD PTR [rbp-104], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 18
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 42
        mov     QWORD PTR [rbp-112], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 17
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 34
        mov     QWORD PTR [rbp-120], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 16
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 26
        mov     QWORD PTR [rbp-128], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 15
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 18
        mov     QWORD PTR [rbp-136], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 14
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 10
        mov     QWORD PTR [rbp-144], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 13
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 2
        mov     QWORD PTR [rbp-152], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 12
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 45
        mov     QWORD PTR [rbp-160], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 11
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 37
        mov     QWORD PTR [rbp-168], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 10
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 29
        mov     QWORD PTR [rbp-176], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 9
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 21
        mov     QWORD PTR [rbp-184], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 8
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 13
        mov     QWORD PTR [rbp-192], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 7
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 5
        mov     QWORD PTR [rbp-200], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 6
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 48
        mov     QWORD PTR [rbp-208], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 5
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 40
        mov     QWORD PTR [rbp-216], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 4
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 32
        mov     QWORD PTR [rbp-224], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 3
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 24
        mov     QWORD PTR [rbp-232], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 2
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 16
        mov     QWORD PTR [rbp-240], rax
        mov     rax, QWORD PTR [rbp-592]
        add     rax, 1
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 8
        mov     QWORD PTR [rbp-248], rax
        mov     rax, QWORD PTR [rbp-592]
        movzx   eax, BYTE PTR [rax]
        mov     BYTE PTR [rbp-249], al
        movzx   edx, BYTE PTR [rbp-249]
        mov     rax, QWORD PTR [rbp-248]
        add     rax, rdx
        mov     QWORD PTR [rbp-264], rax
        mov     rdx, QWORD PTR [rbp-240]
        mov     rax, QWORD PTR [rbp-264]
        add     rax, rdx
        mov     QWORD PTR [rbp-272], rax
        mov     rdx, QWORD PTR [rbp-232]
        mov     rax, QWORD PTR [rbp-272]
        add     rax, rdx
        mov     QWORD PTR [rbp-280], rax
        mov     rdx, QWORD PTR [rbp-224]
        mov     rax, QWORD PTR [rbp-280]
        add     rax, rdx
        mov     QWORD PTR [rbp-288], rax
        mov     rdx, QWORD PTR [rbp-216]
        mov     rax, QWORD PTR [rbp-288]
        add     rax, rdx
        mov     QWORD PTR [rbp-296], rax
        mov     rdx, QWORD PTR [rbp-208]
        mov     rax, QWORD PTR [rbp-296]
        add     rax, rdx
        mov     QWORD PTR [rbp-304], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-304]
        mov     QWORD PTR [rbp-312], rax
        mov     rax, QWORD PTR [rbp-304]
        shr     rax, 51
        mov     BYTE PTR [rbp-313], al
        movzx   edx, BYTE PTR [rbp-313]
        mov     rax, QWORD PTR [rbp-200]
        add     rax, rdx
        mov     QWORD PTR [rbp-328], rax
        mov     rdx, QWORD PTR [rbp-192]
        mov     rax, QWORD PTR [rbp-328]
        add     rax, rdx
        mov     QWORD PTR [rbp-336], rax
        mov     rdx, QWORD PTR [rbp-184]
        mov     rax, QWORD PTR [rbp-336]
        add     rax, rdx
        mov     QWORD PTR [rbp-344], rax
        mov     rdx, QWORD PTR [rbp-176]
        mov     rax, QWORD PTR [rbp-344]
        add     rax, rdx
        mov     QWORD PTR [rbp-352], rax
        mov     rdx, QWORD PTR [rbp-168]
        mov     rax, QWORD PTR [rbp-352]
        add     rax, rdx
        mov     QWORD PTR [rbp-360], rax
        mov     rdx, QWORD PTR [rbp-160]
        mov     rax, QWORD PTR [rbp-360]
        add     rax, rdx
        mov     QWORD PTR [rbp-368], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-368]
        mov     QWORD PTR [rbp-376], rax
        mov     rax, QWORD PTR [rbp-368]
        shr     rax, 51
        mov     BYTE PTR [rbp-377], al
        movzx   edx, BYTE PTR [rbp-377]
        mov     rax, QWORD PTR [rbp-152]
        add     rax, rdx
        mov     QWORD PTR [rbp-392], rax
        mov     rdx, QWORD PTR [rbp-144]
        mov     rax, QWORD PTR [rbp-392]
        add     rax, rdx
        mov     QWORD PTR [rbp-400], rax
        mov     rdx, QWORD PTR [rbp-136]
        mov     rax, QWORD PTR [rbp-400]
        add     rax, rdx
        mov     QWORD PTR [rbp-408], rax
        mov     rdx, QWORD PTR [rbp-128]
        mov     rax, QWORD PTR [rbp-408]
        add     rax, rdx
        mov     QWORD PTR [rbp-416], rax
        mov     rdx, QWORD PTR [rbp-120]
        mov     rax, QWORD PTR [rbp-416]
        add     rax, rdx
        mov     QWORD PTR [rbp-424], rax
        mov     rdx, QWORD PTR [rbp-112]
        mov     rax, QWORD PTR [rbp-424]
        add     rax, rdx
        mov     QWORD PTR [rbp-432], rax
        mov     rdx, QWORD PTR [rbp-104]
        mov     rax, QWORD PTR [rbp-432]
        add     rax, rdx
        mov     QWORD PTR [rbp-440], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-440]
        mov     QWORD PTR [rbp-448], rax
        mov     rax, QWORD PTR [rbp-440]
        shr     rax, 51
        mov     BYTE PTR [rbp-449], al
        movzx   edx, BYTE PTR [rbp-449]
        mov     rax, QWORD PTR [rbp-96]
        add     rax, rdx
        mov     QWORD PTR [rbp-464], rax
        mov     rdx, QWORD PTR [rbp-88]
        mov     rax, QWORD PTR [rbp-464]
        add     rax, rdx
        mov     QWORD PTR [rbp-472], rax
        mov     rdx, QWORD PTR [rbp-80]
        mov     rax, QWORD PTR [rbp-472]
        add     rax, rdx
        mov     QWORD PTR [rbp-480], rax
        mov     rdx, QWORD PTR [rbp-72]
        mov     rax, QWORD PTR [rbp-480]
        add     rax, rdx
        mov     QWORD PTR [rbp-488], rax
        mov     rdx, QWORD PTR [rbp-64]
        mov     rax, QWORD PTR [rbp-488]
        add     rax, rdx
        mov     QWORD PTR [rbp-496], rax
        mov     rdx, QWORD PTR [rbp-56]
        mov     rax, QWORD PTR [rbp-496]
        add     rax, rdx
        mov     QWORD PTR [rbp-504], rax
        movabs  rax, 2251799813685247
        and     rax, QWORD PTR [rbp-504]
        mov     QWORD PTR [rbp-512], rax
        mov     rax, QWORD PTR [rbp-504]
        shr     rax, 51
        mov     BYTE PTR [rbp-513], al
        movzx   edx, BYTE PTR [rbp-513]
        mov     rax, QWORD PTR [rbp-48]
        add     rax, rdx
        mov     QWORD PTR [rbp-528], rax
        mov     rdx, QWORD PTR [rbp-40]
        mov     rax, QWORD PTR [rbp-528]
        add     rax, rdx
        mov     QWORD PTR [rbp-536], rax
        mov     rdx, QWORD PTR [rbp-32]
        mov     rax, QWORD PTR [rbp-536]
        add     rax, rdx
        mov     QWORD PTR [rbp-544], rax
        mov     rdx, QWORD PTR [rbp-24]
        mov     rax, QWORD PTR [rbp-544]
        add     rax, rdx
        mov     QWORD PTR [rbp-552], rax
        mov     rdx, QWORD PTR [rbp-16]
        mov     rax, QWORD PTR [rbp-552]
        add     rax, rdx
        mov     QWORD PTR [rbp-560], rax
        mov     rdx, QWORD PTR [rbp-8]
        mov     rax, QWORD PTR [rbp-560]
        add     rax, rdx
        mov     QWORD PTR [rbp-568], rax
        mov     rax, QWORD PTR [rbp-584]
        mov     rdx, QWORD PTR [rbp-312]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-584]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-376]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-584]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-448]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-584]
        lea     rdx, [rax+24]
        mov     rax, QWORD PTR [rbp-512]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-584]
        lea     rdx, [rax+32]
        mov     rax, QWORD PTR [rbp-568]
        mov     QWORD PTR [rdx], rax
        nop
        leave
        ret