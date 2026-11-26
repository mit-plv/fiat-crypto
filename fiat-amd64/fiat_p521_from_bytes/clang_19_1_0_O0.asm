        .globl  _Z20fiat_p521_from_bytesPmPKh
_Z20fiat_p521_from_bytesPmPKh:
        push    rbp
        mov     rbp, rsp
        sub     rsp, 1016
        mov     qword ptr [rbp - 8], rdi
        mov     qword ptr [rbp - 16], rsi
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 65]
        shl     rax, 56
        mov     qword ptr [rbp - 24], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 64]
        shl     rax, 48
        mov     qword ptr [rbp - 32], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 63]
        shl     rax, 40
        mov     qword ptr [rbp - 40], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 62]
        shl     rax, 32
        mov     qword ptr [rbp - 48], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 61]
        shl     rax, 24
        mov     qword ptr [rbp - 56], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 60]
        shl     rax, 16
        mov     qword ptr [rbp - 64], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 59]
        shl     rax, 8
        mov     qword ptr [rbp - 72], rax
        mov     rax, qword ptr [rbp - 16]
        mov     al, byte ptr [rax + 58]
        mov     byte ptr [rbp - 73], al
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 57]
        shl     rax, 50
        mov     qword ptr [rbp - 88], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 56]
        shl     rax, 42
        mov     qword ptr [rbp - 96], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 55]
        shl     rax, 34
        mov     qword ptr [rbp - 104], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 54]
        shl     rax, 26
        mov     qword ptr [rbp - 112], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 53]
        shl     rax, 18
        mov     qword ptr [rbp - 120], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 52]
        shl     rax, 10
        mov     qword ptr [rbp - 128], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 51]
        shl     rax, 2
        mov     qword ptr [rbp - 136], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 50]
        shl     rax, 52
        mov     qword ptr [rbp - 144], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 49]
        shl     rax, 44
        mov     qword ptr [rbp - 152], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 48]
        shl     rax, 36
        mov     qword ptr [rbp - 160], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 47]
        shl     rax, 28
        mov     qword ptr [rbp - 168], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 46]
        shl     rax, 20
        mov     qword ptr [rbp - 176], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 45]
        shl     rax, 12
        mov     qword ptr [rbp - 184], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 44]
        shl     rax, 4
        mov     qword ptr [rbp - 192], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 43]
        shl     rax, 54
        mov     qword ptr [rbp - 200], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 42]
        shl     rax, 46
        mov     qword ptr [rbp - 208], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 41]
        shl     rax, 38
        mov     qword ptr [rbp - 216], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 40]
        shl     rax, 30
        mov     qword ptr [rbp - 224], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 39]
        shl     rax, 22
        mov     qword ptr [rbp - 232], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 38]
        shl     rax, 14
        mov     qword ptr [rbp - 240], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 37]
        shl     rax, 6
        mov     qword ptr [rbp - 248], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 36]
        shl     rax, 56
        mov     qword ptr [rbp - 256], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 35]
        shl     rax, 48
        mov     qword ptr [rbp - 264], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 34]
        shl     rax, 40
        mov     qword ptr [rbp - 272], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 33]
        shl     rax, 32
        mov     qword ptr [rbp - 280], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 32]
        shl     rax, 24
        mov     qword ptr [rbp - 288], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 31]
        shl     rax, 16
        mov     qword ptr [rbp - 296], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 30]
        shl     rax, 8
        mov     qword ptr [rbp - 304], rax
        mov     rax, qword ptr [rbp - 16]
        mov     al, byte ptr [rax + 29]
        mov     byte ptr [rbp - 305], al
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 28]
        shl     rax, 50
        mov     qword ptr [rbp - 320], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 27]
        shl     rax, 42
        mov     qword ptr [rbp - 328], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 26]
        shl     rax, 34
        mov     qword ptr [rbp - 336], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 25]
        shl     rax, 26
        mov     qword ptr [rbp - 344], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 24]
        shl     rax, 18
        mov     qword ptr [rbp - 352], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 23]
        shl     rax, 10
        mov     qword ptr [rbp - 360], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 22]
        shl     rax, 2
        mov     qword ptr [rbp - 368], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 21]
        shl     rax, 52
        mov     qword ptr [rbp - 376], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 20]
        shl     rax, 44
        mov     qword ptr [rbp - 384], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 19]
        shl     rax, 36
        mov     qword ptr [rbp - 392], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 18]
        shl     rax, 28
        mov     qword ptr [rbp - 400], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 17]
        shl     rax, 20
        mov     qword ptr [rbp - 408], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 16]
        shl     rax, 12
        mov     qword ptr [rbp - 416], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 15]
        shl     rax, 4
        mov     qword ptr [rbp - 424], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 14]
        shl     rax, 54
        mov     qword ptr [rbp - 432], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 13]
        shl     rax, 46
        mov     qword ptr [rbp - 440], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 12]
        shl     rax, 38
        mov     qword ptr [rbp - 448], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 11]
        shl     rax, 30
        mov     qword ptr [rbp - 456], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 10]
        shl     rax, 22
        mov     qword ptr [rbp - 464], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 9]
        shl     rax, 14
        mov     qword ptr [rbp - 472], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 8]
        shl     rax, 6
        mov     qword ptr [rbp - 480], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 7]
        shl     rax, 56
        mov     qword ptr [rbp - 488], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 6]
        shl     rax, 48
        mov     qword ptr [rbp - 496], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 5]
        shl     rax, 40
        mov     qword ptr [rbp - 504], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 4]
        shl     rax, 32
        mov     qword ptr [rbp - 512], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 3]
        shl     rax, 24
        mov     qword ptr [rbp - 520], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 2]
        shl     rax, 16
        mov     qword ptr [rbp - 528], rax
        mov     rax, qword ptr [rbp - 16]
        movzx   eax, byte ptr [rax + 1]
        shl     rax, 8
        mov     qword ptr [rbp - 536], rax
        mov     rax, qword ptr [rbp - 16]
        mov     al, byte ptr [rax]
        mov     byte ptr [rbp - 537], al
        mov     rax, qword ptr [rbp - 536]
        movzx   ecx, byte ptr [rbp - 537]
        add     rax, rcx
        mov     qword ptr [rbp - 552], rax
        mov     rax, qword ptr [rbp - 528]
        add     rax, qword ptr [rbp - 552]
        mov     qword ptr [rbp - 560], rax
        mov     rax, qword ptr [rbp - 520]
        add     rax, qword ptr [rbp - 560]
        mov     qword ptr [rbp - 568], rax
        mov     rax, qword ptr [rbp - 512]
        add     rax, qword ptr [rbp - 568]
        mov     qword ptr [rbp - 576], rax
        mov     rax, qword ptr [rbp - 504]
        add     rax, qword ptr [rbp - 576]
        mov     qword ptr [rbp - 584], rax
        mov     rax, qword ptr [rbp - 496]
        add     rax, qword ptr [rbp - 584]
        mov     qword ptr [rbp - 592], rax
        mov     rax, qword ptr [rbp - 488]
        add     rax, qword ptr [rbp - 592]
        mov     qword ptr [rbp - 600], rax
        movabs  rax, 288230376151711743
        and     rax, qword ptr [rbp - 600]
        mov     qword ptr [rbp - 608], rax
        mov     rax, qword ptr [rbp - 600]
        shr     rax, 58
        mov     byte ptr [rbp - 609], al
        mov     rax, qword ptr [rbp - 480]
        movzx   ecx, byte ptr [rbp - 609]
        add     rax, rcx
        mov     qword ptr [rbp - 624], rax
        mov     rax, qword ptr [rbp - 472]
        add     rax, qword ptr [rbp - 624]
        mov     qword ptr [rbp - 632], rax
        mov     rax, qword ptr [rbp - 464]
        add     rax, qword ptr [rbp - 632]
        mov     qword ptr [rbp - 640], rax
        mov     rax, qword ptr [rbp - 456]
        add     rax, qword ptr [rbp - 640]
        mov     qword ptr [rbp - 648], rax
        mov     rax, qword ptr [rbp - 448]
        add     rax, qword ptr [rbp - 648]
        mov     qword ptr [rbp - 656], rax
        mov     rax, qword ptr [rbp - 440]
        add     rax, qword ptr [rbp - 656]
        mov     qword ptr [rbp - 664], rax
        mov     rax, qword ptr [rbp - 432]
        add     rax, qword ptr [rbp - 664]
        mov     qword ptr [rbp - 672], rax
        movabs  rax, 288230376151711743
        and     rax, qword ptr [rbp - 672]
        mov     qword ptr [rbp - 680], rax
        mov     rax, qword ptr [rbp - 672]
        shr     rax, 58
        mov     byte ptr [rbp - 681], al
        mov     rax, qword ptr [rbp - 424]
        movzx   ecx, byte ptr [rbp - 681]
        add     rax, rcx
        mov     qword ptr [rbp - 696], rax
        mov     rax, qword ptr [rbp - 416]
        add     rax, qword ptr [rbp - 696]
        mov     qword ptr [rbp - 704], rax
        mov     rax, qword ptr [rbp - 408]
        add     rax, qword ptr [rbp - 704]
        mov     qword ptr [rbp - 712], rax
        mov     rax, qword ptr [rbp - 400]
        add     rax, qword ptr [rbp - 712]
        mov     qword ptr [rbp - 720], rax
        mov     rax, qword ptr [rbp - 392]
        add     rax, qword ptr [rbp - 720]
        mov     qword ptr [rbp - 728], rax
        mov     rax, qword ptr [rbp - 384]
        add     rax, qword ptr [rbp - 728]
        mov     qword ptr [rbp - 736], rax
        mov     rax, qword ptr [rbp - 376]
        add     rax, qword ptr [rbp - 736]
        mov     qword ptr [rbp - 744], rax
        movabs  rax, 288230376151711743
        and     rax, qword ptr [rbp - 744]
        mov     qword ptr [rbp - 752], rax
        mov     rax, qword ptr [rbp - 744]
        shr     rax, 58
        mov     byte ptr [rbp - 753], al
        mov     rax, qword ptr [rbp - 368]
        movzx   ecx, byte ptr [rbp - 753]
        add     rax, rcx
        mov     qword ptr [rbp - 768], rax
        mov     rax, qword ptr [rbp - 360]
        add     rax, qword ptr [rbp - 768]
        mov     qword ptr [rbp - 776], rax
        mov     rax, qword ptr [rbp - 352]
        add     rax, qword ptr [rbp - 776]
        mov     qword ptr [rbp - 784], rax
        mov     rax, qword ptr [rbp - 344]
        add     rax, qword ptr [rbp - 784]
        mov     qword ptr [rbp - 792], rax
        mov     rax, qword ptr [rbp - 336]
        add     rax, qword ptr [rbp - 792]
        mov     qword ptr [rbp - 800], rax
        mov     rax, qword ptr [rbp - 328]
        add     rax, qword ptr [rbp - 800]
        mov     qword ptr [rbp - 808], rax
        mov     rax, qword ptr [rbp - 320]
        add     rax, qword ptr [rbp - 808]
        mov     qword ptr [rbp - 816], rax
        mov     rax, qword ptr [rbp - 304]
        movzx   ecx, byte ptr [rbp - 305]
        add     rax, rcx
        mov     qword ptr [rbp - 824], rax
        mov     rax, qword ptr [rbp - 296]
        add     rax, qword ptr [rbp - 824]
        mov     qword ptr [rbp - 832], rax
        mov     rax, qword ptr [rbp - 288]
        add     rax, qword ptr [rbp - 832]
        mov     qword ptr [rbp - 840], rax
        mov     rax, qword ptr [rbp - 280]
        add     rax, qword ptr [rbp - 840]
        mov     qword ptr [rbp - 848], rax
        mov     rax, qword ptr [rbp - 272]
        add     rax, qword ptr [rbp - 848]
        mov     qword ptr [rbp - 856], rax
        mov     rax, qword ptr [rbp - 264]
        add     rax, qword ptr [rbp - 856]
        mov     qword ptr [rbp - 864], rax
        mov     rax, qword ptr [rbp - 256]
        add     rax, qword ptr [rbp - 864]
        mov     qword ptr [rbp - 872], rax
        movabs  rax, 288230376151711743
        and     rax, qword ptr [rbp - 872]
        mov     qword ptr [rbp - 880], rax
        mov     rax, qword ptr [rbp - 872]
        shr     rax, 58
        mov     byte ptr [rbp - 881], al
        mov     rax, qword ptr [rbp - 248]
        movzx   ecx, byte ptr [rbp - 881]
        add     rax, rcx
        mov     qword ptr [rbp - 896], rax
        mov     rax, qword ptr [rbp - 240]
        add     rax, qword ptr [rbp - 896]
        mov     qword ptr [rbp - 904], rax
        mov     rax, qword ptr [rbp - 232]
        add     rax, qword ptr [rbp - 904]
        mov     qword ptr [rbp - 912], rax
        mov     rax, qword ptr [rbp - 224]
        add     rax, qword ptr [rbp - 912]
        mov     qword ptr [rbp - 920], rax
        mov     rax, qword ptr [rbp - 216]
        add     rax, qword ptr [rbp - 920]
        mov     qword ptr [rbp - 928], rax
        mov     rax, qword ptr [rbp - 208]
        add     rax, qword ptr [rbp - 928]
        mov     qword ptr [rbp - 936], rax
        mov     rax, qword ptr [rbp - 200]
        add     rax, qword ptr [rbp - 936]
        mov     qword ptr [rbp - 944], rax
        movabs  rax, 288230376151711743
        and     rax, qword ptr [rbp - 944]
        mov     qword ptr [rbp - 952], rax
        mov     rax, qword ptr [rbp - 944]
        shr     rax, 58
        mov     byte ptr [rbp - 953], al
        mov     rax, qword ptr [rbp - 192]
        movzx   ecx, byte ptr [rbp - 953]
        add     rax, rcx
        mov     qword ptr [rbp - 968], rax
        mov     rax, qword ptr [rbp - 184]
        add     rax, qword ptr [rbp - 968]
        mov     qword ptr [rbp - 976], rax
        mov     rax, qword ptr [rbp - 176]
        add     rax, qword ptr [rbp - 976]
        mov     qword ptr [rbp - 984], rax
        mov     rax, qword ptr [rbp - 168]
        add     rax, qword ptr [rbp - 984]
        mov     qword ptr [rbp - 992], rax
        mov     rax, qword ptr [rbp - 160]
        add     rax, qword ptr [rbp - 992]
        mov     qword ptr [rbp - 1000], rax
        mov     rax, qword ptr [rbp - 152]
        add     rax, qword ptr [rbp - 1000]
        mov     qword ptr [rbp - 1008], rax
        mov     rax, qword ptr [rbp - 144]
        add     rax, qword ptr [rbp - 1008]
        mov     qword ptr [rbp - 1016], rax
        movabs  rax, 288230376151711743
        and     rax, qword ptr [rbp - 1016]
        mov     qword ptr [rbp - 1024], rax
        mov     rax, qword ptr [rbp - 1016]
        shr     rax, 58
        mov     byte ptr [rbp - 1025], al
        mov     rax, qword ptr [rbp - 136]
        movzx   ecx, byte ptr [rbp - 1025]
        add     rax, rcx
        mov     qword ptr [rbp - 1040], rax
        mov     rax, qword ptr [rbp - 128]
        add     rax, qword ptr [rbp - 1040]
        mov     qword ptr [rbp - 1048], rax
        mov     rax, qword ptr [rbp - 120]
        add     rax, qword ptr [rbp - 1048]
        mov     qword ptr [rbp - 1056], rax
        mov     rax, qword ptr [rbp - 112]
        add     rax, qword ptr [rbp - 1056]
        mov     qword ptr [rbp - 1064], rax
        mov     rax, qword ptr [rbp - 104]
        add     rax, qword ptr [rbp - 1064]
        mov     qword ptr [rbp - 1072], rax
        mov     rax, qword ptr [rbp - 96]
        add     rax, qword ptr [rbp - 1072]
        mov     qword ptr [rbp - 1080], rax
        mov     rax, qword ptr [rbp - 88]
        add     rax, qword ptr [rbp - 1080]
        mov     qword ptr [rbp - 1088], rax
        mov     rax, qword ptr [rbp - 72]
        movzx   ecx, byte ptr [rbp - 73]
        add     rax, rcx
        mov     qword ptr [rbp - 1096], rax
        mov     rax, qword ptr [rbp - 64]
        add     rax, qword ptr [rbp - 1096]
        mov     qword ptr [rbp - 1104], rax
        mov     rax, qword ptr [rbp - 56]
        add     rax, qword ptr [rbp - 1104]
        mov     qword ptr [rbp - 1112], rax
        mov     rax, qword ptr [rbp - 48]
        add     rax, qword ptr [rbp - 1112]
        mov     qword ptr [rbp - 1120], rax
        mov     rax, qword ptr [rbp - 40]
        add     rax, qword ptr [rbp - 1120]
        mov     qword ptr [rbp - 1128], rax
        mov     rax, qword ptr [rbp - 32]
        add     rax, qword ptr [rbp - 1128]
        mov     qword ptr [rbp - 1136], rax
        mov     rax, qword ptr [rbp - 24]
        add     rax, qword ptr [rbp - 1136]
        mov     qword ptr [rbp - 1144], rax
        mov     rcx, qword ptr [rbp - 608]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax], rcx
        mov     rcx, qword ptr [rbp - 680]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 8], rcx
        mov     rcx, qword ptr [rbp - 752]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 16], rcx
        mov     rcx, qword ptr [rbp - 816]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 24], rcx
        mov     rcx, qword ptr [rbp - 880]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 32], rcx
        mov     rcx, qword ptr [rbp - 952]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 40], rcx
        mov     rcx, qword ptr [rbp - 1024]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 48], rcx
        mov     rcx, qword ptr [rbp - 1088]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 56], rcx
        mov     rcx, qword ptr [rbp - 1144]
        mov     rax, qword ptr [rbp - 8]
        mov     qword ptr [rax + 64], rcx
        add     rsp, 1016
        pop     rbp
        ret
