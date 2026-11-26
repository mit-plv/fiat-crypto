        .globl  _Z24fiat_poly1305_from_bytesPmPKh
_Z24fiat_poly1305_from_bytesPmPKh:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 184
        mov     qword ptr [rbp - 8], rdi
        mov     qword ptr [rbp - 16], rsi
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 16]
        shl     rax, 41
        mov     qword ptr [rbp - 24], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 15]
        shl     rax, 33
        mov     qword ptr [rbp - 32], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 14]
        shl     rax, 25
        mov     qword ptr [rbp - 40], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 13]
        shl     rax, 17
        mov     qword ptr [rbp - 48], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 12]
        shl     rax, 9
        mov     qword ptr [rbp - 56], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 11]
        shl     rax
        mov     qword ptr [rbp - 64], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 10]
        shl     rax, 36
        mov     qword ptr [rbp - 72], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 9]
        shl     rax, 28
        mov     qword ptr [rbp - 80], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 8]
        shl     rax, 20
        mov     qword ptr [rbp - 88], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 7]
        shl     rax, 12
        mov     qword ptr [rbp - 96], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 6]
        shl     rax, 4
        mov     qword ptr [rbp - 104], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 5]
        shl     rax, 40
        mov     qword ptr [rbp - 112], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 4]
        shl     rax, 32
        mov     qword ptr [rbp - 120], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 3]
        shl     rax, 24
        mov     qword ptr [rbp - 128], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 2]
        shl     rax, 16
        mov     qword ptr [rbp - 136], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 1]
        shl     rax, 8
        mov     qword ptr [rbp - 144], rax
        mov     rax, qword ptr [rbp - 16]
        mov     al, byte ptr [rax]
        mov     byte ptr [rbp - 145], al
        mov     rax, qword ptr [rbp - 144]
        movzx   ecx, byte ptr [rbp - 145]
        add     rax, rcx
        mov     qword ptr [rbp - 160], rax
        mov     rax, qword ptr [rbp - 136]
        add     rax, qword ptr [rbp - 160]
        mov     qword ptr [rbp - 168], rax
        mov     rax, qword ptr [rbp - 128]
        add     rax, qword ptr [rbp - 168]
        mov     qword ptr [rbp - 176], rax
        mov     rax, qword ptr [rbp - 120]
        add     rax, qword ptr [rbp - 176]
        mov     qword ptr [rbp - 184], rax
        mov     rax, qword ptr [rbp - 112]
        add     rax, qword ptr [rbp - 184]
        mov     qword ptr [rbp - 192], rax
        movabs  rax, 17592186044415
        and     rax, qword ptr [rbp - 192]
        mov     qword ptr [rbp - 200], rax
        mov     rax, qword ptr [rbp - 192]
        shr     rax, 44
        mov     byte ptr [rbp - 201], al
        mov     rax, qword ptr [rbp - 104]
        movzx   ecx, byte ptr [rbp - 201]
        add     rax, rcx
        mov     qword ptr [rbp - 216], rax
        mov     rax, qword ptr [rbp - 96]
        add     rax, qword ptr [rbp - 216]
        mov     qword ptr [rbp - 224], rax
        mov     rax, qword ptr [rbp - 88]
        add     rax, qword ptr [rbp - 224]
        mov     qword ptr [rbp - 232], rax
        mov     rax, qword ptr [rbp - 80]
        add     rax, qword ptr [rbp - 232]
        mov     qword ptr [rbp - 240], rax
        mov     rax, qword ptr [rbp - 72]
        add     rax, qword ptr [rbp - 240]
        mov     qword ptr [rbp - 248], rax
        movabs  rax, 8796093022207
        and     rax, qword ptr [rbp - 248]
        mov     qword ptr [rbp - 256], rax
        mov     rax, qword ptr [rbp - 248]
        shr     rax, 43
        mov     byte ptr [rbp - 257], al
        mov     rax, qword ptr [rbp - 64]
        movzx   ecx, byte ptr [rbp - 257]
        add     rax, rcx
        mov     qword ptr [rbp - 272], rax
        mov     rax, qword ptr [rbp - 56]
        add     rax, qword ptr [rbp - 272]
        mov     qword ptr [rbp - 280], rax
        mov     rax, qword ptr [rbp - 48]
        add     rax, qword ptr [rbp - 280]
        mov     qword ptr [rbp - 288], rax
        mov     rax, qword ptr [rbp - 40]
        add     rax, qword ptr [rbp - 288]
        mov     qword ptr [rbp - 296], rax
        mov     rax, qword ptr [rbp - 32]
        add     rax, qword ptr [rbp - 296]
        mov     qword ptr [rbp - 304], rax
        mov     rax, qword ptr [rbp - 24]
        add     rax, qword ptr [rbp - 304]
        mov     qword ptr [rbp - 312], rax
        mov     rcx, qword ptr [rbp - 200]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax], rcx
        mov     rcx, qword ptr [rbp - 256]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 8], rcx
        mov     rcx, qword ptr [rbp - 312]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 16], rcx
        add     rsp, 184
        pop     rbp
        ret