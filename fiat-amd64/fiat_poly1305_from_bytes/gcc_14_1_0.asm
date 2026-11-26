        .globl  _Z24fiat_poly1305_from_bytesPmPKh
_Z24fiat_poly1305_from_bytesPmPKh:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 200
        mov     QWORD PTR [rbp-312], rdi
        mov     QWORD PTR [rbp-320], rsi
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 16
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 41
        mov     QWORD PTR [rbp-8], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 15
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 33
        mov     QWORD PTR [rbp-16], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 14
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 25
        mov     QWORD PTR [rbp-24], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 13
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 17
        mov     QWORD PTR [rbp-32], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 12
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 9
        mov     QWORD PTR [rbp-40], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 11
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        add     rax, rax
        mov     QWORD PTR [rbp-48], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 10
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 36
        mov     QWORD PTR [rbp-56], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 9
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 28
        mov     QWORD PTR [rbp-64], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 8
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 20
        mov     QWORD PTR [rbp-72], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 7
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 12
        mov     QWORD PTR [rbp-80], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 6
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 4
        mov     QWORD PTR [rbp-88], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 5
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 40
        mov     QWORD PTR [rbp-96], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 4
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 32
        mov     QWORD PTR [rbp-104], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 3
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 24
        mov     QWORD PTR [rbp-112], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 2
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 16
        mov     QWORD PTR [rbp-120], rax
        mov     rax, QWORD PTR [rbp-320]
        add     rax, 1
        movzx   eax, BYTE PTR [rax]
        movzx   eax, al
        sal     rax, 8
        mov     QWORD PTR [rbp-128], rax
        mov     rax, QWORD PTR [rbp-320]
        movzx   eax, BYTE PTR [rax]
        mov     BYTE PTR [rbp-129], al
        movzx   edx, BYTE PTR [rbp-129]
        mov     rax, QWORD PTR [rbp-128]
        add     rax, rdx
        mov     QWORD PTR [rbp-144], rax
        mov     rdx, QWORD PTR [rbp-120]
        mov     rax, QWORD PTR [rbp-144]
        add     rax, rdx
        mov     QWORD PTR [rbp-152], rax
        mov     rdx, QWORD PTR [rbp-112]
        mov     rax, QWORD PTR [rbp-152]
        add     rax, rdx
        mov     QWORD PTR [rbp-160], rax
        mov     rdx, QWORD PTR [rbp-104]
        mov     rax, QWORD PTR [rbp-160]
        add     rax, rdx
        mov     QWORD PTR [rbp-168], rax
        mov     rdx, QWORD PTR [rbp-96]
        mov     rax, QWORD PTR [rbp-168]
        add     rax, rdx
        mov     QWORD PTR [rbp-176], rax
        movabs  rax, 17592186044415
        and     rax, QWORD PTR [rbp-176]
        mov     QWORD PTR [rbp-184], rax
        mov     rax, QWORD PTR [rbp-176]
        shr     rax, 44
        mov     BYTE PTR [rbp-185], al
        movzx   edx, BYTE PTR [rbp-185]
        mov     rax, QWORD PTR [rbp-88]
        add     rax, rdx
        mov     QWORD PTR [rbp-200], rax
        mov     rdx, QWORD PTR [rbp-80]
        mov     rax, QWORD PTR [rbp-200]
        add     rax, rdx
        mov     QWORD PTR [rbp-208], rax
        mov     rdx, QWORD PTR [rbp-72]
        mov     rax, QWORD PTR [rbp-208]
        add     rax, rdx
        mov     QWORD PTR [rbp-216], rax
        mov     rdx, QWORD PTR [rbp-64]
        mov     rax, QWORD PTR [rbp-216]
        add     rax, rdx
        mov     QWORD PTR [rbp-224], rax
        mov     rdx, QWORD PTR [rbp-56]
        mov     rax, QWORD PTR [rbp-224]
        add     rax, rdx
        mov     QWORD PTR [rbp-232], rax
        movabs  rax, 8796093022207
        and     rax, QWORD PTR [rbp-232]
        mov     QWORD PTR [rbp-240], rax
        mov     rax, QWORD PTR [rbp-232]
        shr     rax, 43
        mov     BYTE PTR [rbp-241], al
        movzx   edx, BYTE PTR [rbp-241]
        mov     rax, QWORD PTR [rbp-48]
        add     rax, rdx
        mov     QWORD PTR [rbp-256], rax
        mov     rdx, QWORD PTR [rbp-40]
        mov     rax, QWORD PTR [rbp-256]
        add     rax, rdx
        mov     QWORD PTR [rbp-264], rax
        mov     rdx, QWORD PTR [rbp-32]
        mov     rax, QWORD PTR [rbp-264]
        add     rax, rdx
        mov     QWORD PTR [rbp-272], rax
        mov     rdx, QWORD PTR [rbp-24]
        mov     rax, QWORD PTR [rbp-272]
        add     rax, rdx
        mov     QWORD PTR [rbp-280], rax
        mov     rdx, QWORD PTR [rbp-16]
        mov     rax, QWORD PTR [rbp-280]
        add     rax, rdx
        mov     QWORD PTR [rbp-288], rax
        mov     rdx, QWORD PTR [rbp-8]
        mov     rax, QWORD PTR [rbp-288]
        add     rax, rdx
        mov     QWORD PTR [rbp-296], rax
        mov     rax, QWORD PTR [rbp-312]
        mov     rdx, QWORD PTR [rbp-184]
        mov     QWORD PTR [rax], rdx
        mov     rax, QWORD PTR [rbp-312]
        lea     rdx, [rax+8]
        mov     rax, QWORD PTR [rbp-240]
        mov     QWORD PTR [rdx], rax
        mov     rax, QWORD PTR [rbp-312]
        lea     rdx, [rax+16]
        mov     rax, QWORD PTR [rbp-296]
        mov     QWORD PTR [rdx], rax
        nop
        leave
        ret