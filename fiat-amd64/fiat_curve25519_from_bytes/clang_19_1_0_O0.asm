        .globl  _Z21fiat_25519_from_bytesPmPKh
_Z21fiat_25519_from_bytesPmPKh:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 456
        mov     qword ptr [rbp - 8], rdi
        mov     qword ptr [rbp - 16], rsi
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 31]
        shl     rax, 44
        mov     qword ptr [rbp - 24], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 30]
        shl     rax, 36
        mov     qword ptr [rbp - 32], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 29]
        shl     rax, 28
        mov     qword ptr [rbp - 40], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 28]
        shl     rax, 20
        mov     qword ptr [rbp - 48], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 27]
        shl     rax, 12
        mov     qword ptr [rbp - 56], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 26]
        shl     rax, 4
        mov     qword ptr [rbp - 64], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 25]
        shl     rax, 47
        mov     qword ptr [rbp - 72], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 24]
        shl     rax, 39
        mov     qword ptr [rbp - 80], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 23]
        shl     rax, 31
        mov     qword ptr [rbp - 88], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 22]
        shl     rax, 23
        mov     qword ptr [rbp - 96], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 21]
        shl     rax, 15
        mov     qword ptr [rbp - 104], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 20]
        shl     rax, 7
        mov     qword ptr [rbp - 112], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 19]
        shl     rax, 50
        mov     qword ptr [rbp - 120], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 18]
        shl     rax, 42
        mov     qword ptr [rbp - 128], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 17]
        shl     rax, 34
        mov     qword ptr [rbp - 136], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 16]
        shl     rax, 26
        mov     qword ptr [rbp - 144], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 15]
        shl     rax, 18
        mov     qword ptr [rbp - 152], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 14]
        shl     rax, 10
        mov     qword ptr [rbp - 160], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 13]
        shl     rax, 2
        mov     qword ptr [rbp - 168], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 12]
        shl     rax, 45
        mov     qword ptr [rbp - 176], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 11]
        shl     rax, 37
        mov     qword ptr [rbp - 184], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 10]
        shl     rax, 29
        mov     qword ptr [rbp - 192], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 9]
        shl     rax, 21
        mov     qword ptr [rbp - 200], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 8]
        shl     rax, 13
        mov     qword ptr [rbp - 208], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 7]
        shl     rax, 5
        mov     qword ptr [rbp - 216], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 6]
        shl     rax, 48
        mov     qword ptr [rbp - 224], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 5]
        shl     rax, 40
        mov     qword ptr [rbp - 232], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 4]
        shl     rax, 32
        mov     qword ptr [rbp - 240], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 3]
        shl     rax, 24
        mov     qword ptr [rbp - 248], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 2]
        shl     rax, 16
        mov     qword ptr [rbp - 256], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 1]
        shl     rax, 8
        mov     qword ptr [rbp - 264], rax
        mov     rax, qword ptr [rbp - 16]
        mov     al, byte ptr [rax]
        mov     byte ptr [rbp - 265], al
        mov     rax, qword ptr [rbp - 264]
        movzx   ecx, byte ptr [rbp - 265]
        add     rax, rcx
        mov     qword ptr [rbp - 280], rax
        mov     rax, qword ptr [rbp - 256]
        add     rax, qword ptr [rbp - 280]
        mov     qword ptr [rbp - 288], rax
        mov     rax, qword ptr [rbp - 248]
        add     rax, qword ptr [rbp - 288]
        mov     qword ptr [rbp - 296], rax
        mov     rax, qword ptr [rbp - 240]
        add     rax, qword ptr [rbp - 296]
        mov     qword ptr [rbp - 304], rax
        mov     rax, qword ptr [rbp - 232]
        add     rax, qword ptr [rbp - 304]
        mov     qword ptr [rbp - 312], rax
        mov     rax, qword ptr [rbp - 224]
        add     rax, qword ptr [rbp - 312]
        mov     qword ptr [rbp - 320], rax
        movabs  rax, 2251799813685247
        and     rax, qword ptr [rbp - 320]
        mov     qword ptr [rbp - 328], rax
        mov     rax, qword ptr [rbp - 320]
        shr     rax, 51
        mov     byte ptr [rbp - 329], al
        mov     rax, qword ptr [rbp - 216]
        movzx   ecx, byte ptr [rbp - 329]
        add     rax, rcx
        mov     qword ptr [rbp - 344], rax
        mov     rax, qword ptr [rbp - 208]
        add     rax, qword ptr [rbp - 344]
        mov     qword ptr [rbp - 352], rax
        mov     rax, qword ptr [rbp - 200]
        add     rax, qword ptr [rbp - 352]
        mov     qword ptr [rbp - 360], rax
        mov     rax, qword ptr [rbp - 192]
        add     rax, qword ptr [rbp - 360]
        mov     qword ptr [rbp - 368], rax
        mov     rax, qword ptr [rbp - 184]
        add     rax, qword ptr [rbp - 368]
        mov     qword ptr [rbp - 376], rax
        mov     rax, qword ptr [rbp - 176]
        add     rax, qword ptr [rbp - 376]
        mov     qword ptr [rbp - 384], rax
        movabs  rax, 2251799813685247
        and     rax, qword ptr [rbp - 384]
        mov     qword ptr [rbp - 392], rax
        mov     rax, qword ptr [rbp - 384]
        shr     rax, 51
        mov     byte ptr [rbp - 393], al
        mov     rax, qword ptr [rbp - 168]
        movzx   ecx, byte ptr [rbp - 393]
        add     rax, rcx
        mov     qword ptr [rbp - 408], rax
        mov     rax, qword ptr [rbp - 160]
        add     rax, qword ptr [rbp - 408]
        mov     qword ptr [rbp - 416], rax
        mov     rax, qword ptr [rbp - 152]
        add     rax, qword ptr [rbp - 416]
        mov     qword ptr [rbp - 424], rax
        mov     rax, qword ptr [rbp - 144]
        add     rax, qword ptr [rbp - 424]
        mov     qword ptr [rbp - 432], rax
        mov     rax, qword ptr [rbp - 136]
        add     rax, qword ptr [rbp - 432]
        mov     qword ptr [rbp - 440], rax
        mov     rax, qword ptr [rbp - 128]
        add     rax, qword ptr [rbp - 440]
        mov     qword ptr [rbp - 448], rax
        mov     rax, qword ptr [rbp - 120]
        add     rax, qword ptr [rbp - 448]
        mov     qword ptr [rbp - 456], rax
        movabs  rax, 2251799813685247
        and     rax, qword ptr [rbp - 456]
        mov     qword ptr [rbp - 464], rax
        mov     rax, qword ptr [rbp - 456]
        shr     rax, 51
        mov     byte ptr [rbp - 465], al
        mov     rax, qword ptr [rbp - 112]
        movzx   ecx, byte ptr [rbp - 465]
        add     rax, rcx
        mov     qword ptr [rbp - 480], rax
        mov     rax, qword ptr [rbp - 104]
        add     rax, qword ptr [rbp - 480]
        mov     qword ptr [rbp - 488], rax
        mov     rax, qword ptr [rbp - 96]
        add     rax, qword ptr [rbp - 488]
        mov     qword ptr [rbp - 496], rax
        mov     rax, qword ptr [rbp - 88]
        add     rax, qword ptr [rbp - 496]
        mov     qword ptr [rbp - 504], rax
        mov     rax, qword ptr [rbp - 80]
        add     rax, qword ptr [rbp - 504]
        mov     qword ptr [rbp - 512], rax
        mov     rax, qword ptr [rbp - 72]
        add     rax, qword ptr [rbp - 512]
        mov     qword ptr [rbp - 520], rax
        movabs  rax, 2251799813685247
        and     rax, qword ptr [rbp - 520]
        mov     qword ptr [rbp - 528], rax
        mov     rax, qword ptr [rbp - 520]
        shr     rax, 51
        mov     byte ptr [rbp - 529], al
        mov     rax, qword ptr [rbp - 64]
        movzx   ecx, byte ptr [rbp - 529]
        add     rax, rcx
        mov     qword ptr [rbp - 544], rax
        mov     rax, qword ptr [rbp - 56]
        add     rax, qword ptr [rbp - 544]
        mov     qword ptr [rbp - 552], rax
        mov     rax, qword ptr [rbp - 48]
        add     rax, qword ptr [rbp - 552]
        mov     qword ptr [rbp - 560], rax
        mov     rax, qword ptr [rbp - 40]
        add     rax, qword ptr [rbp - 560]
        mov     qword ptr [rbp - 568], rax
        mov     rax, qword ptr [rbp - 32]
        add     rax, qword ptr [rbp - 568]
        mov     qword ptr [rbp - 576], rax
        mov     rax, qword ptr [rbp - 24]
        add     rax, qword ptr [rbp - 576]
        mov     qword ptr [rbp - 584], rax
        mov     rcx, qword ptr [rbp - 328]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax], rcx
        mov     rcx, qword ptr [rbp - 392]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 8], rcx
        mov     rcx, qword ptr [rbp - 464]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 16], rcx
        mov     rcx, qword ptr [rbp - 528]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 24], rcx
        mov     rcx, qword ptr [rbp - 584]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 32], rcx
        add     rsp, 456
        pop     rbp
        ret