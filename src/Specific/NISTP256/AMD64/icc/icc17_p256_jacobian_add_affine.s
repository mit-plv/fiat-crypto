.intel_syntax noprefix
.section .text
.globl p256_jacobian_add_affine
.type p256_jacobian_add_affine, @function
p256_jacobian_add_affine:
        push      r12                                           #306.3
        push      r13                                           #306.3
        push      r14                                           #306.3
        push      r15                                           #306.3
        push      rbx                                           #306.3
        push      rbp                                           #306.3
        sub       rsp, 424                                      #306.3
        mov       QWORD PTR [104+rsp], rdx                      #306.3[spill]
        pxor      xmm0, xmm0                                    #315.20
        mov       QWORD PTR [96+rsp], rsi                       #306.3[spill]
        mov       QWORD PTR [112+rsp], rdi                      #306.3[spill]
        movups    XMMWORD PTR [64+rsp], xmm0                    #315.20
        movups    XMMWORD PTR [80+rsp], xmm0                    #315.20
        mov       r8, rdi                                       #315.41
        mov       r15, -1                                       #196.33
        xor       r9d, r9d                                      #192.32
        vpxor     xmm0, xmm0, xmm0                              #317.20
        mov       r10, QWORD PTR [64+r8]                        #315.62
        mov       rdx, r10                                      #188.33
        mov       r11, QWORD PTR [72+r8]                        #315.55
        mov       rdi, QWORD PTR [88+r8]                        #315.41
        mov       rsi, QWORD PTR [80+r8]                        #315.48
        mulx      r13, r12, r10                                 #188.33
        mulx      r8, rbp, r11                                  #189.33
        adcx      r12, r8                                       #192.32
        mov       QWORD PTR [168+rsp], rsi                      #315.48[spill]
        mulx      rbx, rsi, rsi                                 #190.33
        adcx      rbp, rbx                                      #193.32
        mov       rbx, 0x0ffffffff                              #197.33
        mulx      rcx, rax, rdi                                 #191.33
        mov       rdx, r13                                      #196.33
        adcx      rsi, rcx                                      #194.32
        mov       rcx, 0xffffffff00000001                       #198.33
        mov       QWORD PTR [160+rsp], rdi                      #315.41[spill]
        mov       edi, 0                                        #192.32
        mov       r8d, edi                                      #194.32
        setb      r8b                                           #194.32
        adox      r9d, edi                                      #195.30
        mov       r9d, edi                                      #195.30
        adox      r8, rax                                       #195.30
        mulx      r15, r14, r15                                 #196.33
        seto      r9b                                           #195.30
        clc                                                     #199.32
        mulx      r9, rax, rbx                                  #197.33
        adcx      r14, r9                                       #199.32
        mov       r9d, 0                                        #200.32
        mulx      rcx, rbx, rcx                                 #198.33
        mov       edx, edi                                      #202.30
        adcx      rax, r9                                       #200.32
        mov       QWORD PTR [176+rsp], r11                      #315.55[spill]
        adcx      rcx, r9                                       #201.32
        mov       r9d, edi                                      #201.32
        mov       QWORD PTR [152+rsp], r10                      #315.62[spill]
        setb      r9b                                           #201.32
        adox      edx, edi                                      #202.30
        mov       rdx, r11                                      #208.33
        adox      r9, rbx                                       #202.30
        clc                                                     #203.30
        adcx      r13, r15                                      #203.30
        mulx      r15, r13, QWORD PTR [168+rsp]                 #210.33[spill]
        adcx      r12, r14                                      #204.32
        adcx      rbp, rax                                      #205.32
        mulx      rax, r14, r11                                 #209.33
        mov       r11d, edi                                     #212.32
        adcx      rsi, rcx                                      #206.32
        mulx      r10, rcx, r10                                 #208.33
        adcx      r8, r9                                        #207.32
        mov       r9d, edi                                      #207.32
        mulx      rdx, rbx, QWORD PTR [160+rsp]                 #211.33[spill]
        setb      r9b                                           #207.32
        adox      r11d, edi                                     #212.32
        mov       r11, 0xffffffff00000001                       #223.35
        adox      rcx, rax                                      #212.32
        mov       eax, edi                                      #214.32
        adox      r14, r15                                      #213.32
        mov       r15d, edi                                     #216.34
        adox      r13, rdx                                      #214.32
        seto      al                                            #214.32
        clc                                                     #215.30
        adcx      rax, rbx                                      #215.30
        adox      r15d, edi                                     #216.34
        mov       ebx, edi                                      #220.34
        adox      r12, r10                                      #216.34
        mov       rdx, r12                                      #221.35
        adox      rbp, rcx                                      #217.34
        mov       rcx, -1                                       #221.35
        mulx      r15, r10, rcx                                 #221.35
        adox      rsi, r14                                      #218.34
        mov       r14, 0x0ffffffff                              #222.35
        adox      r8, r13                                       #219.34
        adox      r9, rax                                       #220.34
        mulx      r13, rax, r14                                 #222.35
        mov       r14d, 0                                       #225.34
        seto      bl                                            #220.34
        clc                                                     #224.34
        adcx      r10, r13                                      #224.34
        mulx      rcx, r13, r11                                 #223.35
        mov       r11d, edi                                     #227.31
        adcx      rax, r14                                      #225.34
        mov       rdx, QWORD PTR [168+rsp]                      #234.35[spill]
        adcx      rcx, r14                                      #226.34
        mov       r14d, edi                                     #226.34
        setb      r14b                                          #226.34
        adox      r11d, edi                                     #227.31
        adox      r14, r13                                      #227.31
        mov       r13d, edi                                     #238.34
        clc                                                     #228.31
        adcx      r12, r15                                      #228.31
        mulx      r15, r11, rdx                                 #236.35
        adcx      rbp, r10                                      #229.34
        mov       r10d, edi                                     #232.34
        adcx      rsi, rax                                      #230.34
        adcx      r8, rcx                                       #231.34
        adcx      r9, r14                                       #232.34
        mulx      rax, r14, QWORD PTR [176+rsp]                 #235.35[spill]
        setb      r10b                                          #232.34
        adox      r13d, edi                                     #238.34
        mov       DWORD PTR [32+rsp], r10d                      #232.34[spill]
        mulx      r10, r12, QWORD PTR [152+rsp]                 #234.35[spill]
        adox      r12, rax                                      #238.34
        mov       eax, edi                                      #240.34
        mulx      rdx, rcx, QWORD PTR [160+rsp]                 #237.35[spill]
        adox      r14, r15                                      #239.34
        mov       r15d, edi                                     #242.34
        adox      r11, rdx                                      #240.34
        seto      al                                            #240.34
        clc                                                     #241.31
        adcx      rax, rcx                                      #241.31
        adox      r15d, edi                                     #242.34
        mov       r15, 0x0ffffffff                              #248.35
        adox      rbp, r10                                      #242.34
        mov       rdx, rbp                                      #247.35
        adox      rsi, r12                                      #243.34
        mov       r12d, edi                                     #245.34
        mulx      r10, r15, r15                                 #248.35
        adox      r8, r14                                       #244.34
        adox      r9, r11                                       #245.34
        seto      r12b                                          #245.34
        xor       ecx, ecx                                      #245.34
        add       ebx, DWORD PTR [32+rsp]                       #246.34[spill]
        cmp       edi, r12d                                     #246.34
        mov       r12, 0xffffffff00000001                       #249.35
        adcx      rbx, rax                                      #246.34
        mov       rax, -1                                       #247.35
        mulx      r14, r13, rax                                 #247.35
        mulx      r12, r11, r12                                 #249.35
        mov       edx, edi                                      #250.34
        setb      cl                                            #246.34
        adox      edx, edi                                      #250.34
        mov       rdx, QWORD PTR [160+rsp]                      #260.35[spill]
        adox      r13, r10                                      #250.34
        mov       r10d, 0                                       #251.34
        adox      r15, r10                                      #251.34
        adox      r12, r10                                      #252.34
        mov       r10d, edi                                     #252.34
        seto      r10b                                          #252.34
        clc                                                     #253.31
        adcx      r10, r11                                      #253.31
        mov       r11d, edi                                     #254.31
        adox      r11d, edi                                     #254.31
        adox      rbp, r14                                      #254.31
        adox      rsi, r13                                      #255.34
        mov       r13d, edi                                     #258.34
        adox      r8, r15                                       #256.34
        mulx      rbp, r15, QWORD PTR [176+rsp]                 #261.35[spill]
        adox      r9, r12                                       #257.34
        mulx      r12, r11, QWORD PTR [152+rsp]                 #260.35[spill]
        adox      rbx, r10                                      #258.34
        seto      r13b                                          #258.34
        clc                                                     #264.34
        adcx      r11, rbp                                      #264.34
        mulx      rbp, r14, QWORD PTR [168+rsp]                 #262.35[spill]
        adcx      r15, rbp                                      #265.34
        mulx      rbp, r10, rdx                                 #263.35
        mov       edx, edi                                      #267.31
        adcx      r14, rbp                                      #266.34
        mov       ebp, edi                                      #266.34
        setb      bpl                                           #266.34
        adox      edx, edi                                      #267.31
        adox      rbp, r10                                      #267.31
        clc                                                     #268.34
        adcx      rsi, r12                                      #268.34
        mov       rdx, rsi                                      #273.35
        adcx      r8, r11                                       #269.34
        adcx      r9, r15                                       #270.34
        mov       r15, 0x0ffffffff                              #274.35
        mulx      r15, r11, r15                                 #274.35
        adcx      rbx, r14                                      #271.34
        mov       r14d, edi                                     #271.34
        setb      r14b                                          #271.34
        xor       r10d, r10d                                    #271.34
        add       ecx, r13d                                     #272.34
        cmp       edi, r14d                                     #272.34
        mov       r13, 0xffffffff00000001                       #275.35
        mulx      r14, r12, rax                                 #273.35
        adcx      rcx, rbp                                      #272.34
        mulx      rbp, r13, r13                                 #275.35
        mov       edx, edi                                      #276.34
        setb      r10b                                          #272.34
        adox      edx, edi                                      #276.34
        mov       edx, edi                                      #278.34
        adox      r12, r15                                      #276.34
        mov       r15d, 0                                       #277.34
        adox      r11, r15                                      #277.34
        adox      rbp, r15                                      #278.34
        seto      dl                                            #278.34
        clc                                                     #279.31
        adcx      rdx, r13                                      #279.31
        mov       r13d, edi                                     #280.31
        adox      r13d, edi                                     #280.31
        adox      rsi, r14                                      #280.31
        mov       esi, edi                                      #284.34
        adox      r8, r12                                       #281.34
        adox      r9, r11                                       #282.34
        mov       r11, 0xffffffff00000001                       #289.34
        adox      rbx, rbp                                      #283.34
        mov       rbp, r9                                       #287.34
        adox      rcx, rdx                                      #284.34
        mov       rdx, rcx                                      #289.34
        seto      sil                                           #284.34
        xor       r12d, r12d                                    #284.34
        add       r10d, esi                                     #290.31
        mov       rsi, r8                                       #286.34
        sub       rsi, rax                                      #286.34
        mov       rax, 0x0ffffffff                              #287.34
        sbb       rbp, rax                                      #287.34
        mov       rax, rbx                                      #288.34
        sbb       rax, r15                                      #288.34
        sbb       rdx, r11                                      #289.34
        setb      r12b                                          #289.34
        cmp       edi, r12d                                     #290.31
        sbb       r10, r15                                      #290.31
        setb      dil                                           #290.31
        dec       rdi                                           #9.35
        and       rdx, rdi                                      #10.31
        and       rax, rdi                                      #10.31
        and       rbp, rdi                                      #10.31
        and       rsi, rdi                                      #10.31
        not       rdi                                           #10.43
        and       rcx, rdi                                      #10.60
        and       rbx, rdi                                      #10.60
        and       r9, rdi                                       #10.60
        and       rdi, r8                                       #10.60
        or        rdx, rcx                                      #10.60
        or        rax, rbx                                      #10.60
        or        rbp, r9                                       #10.60
        or        rsi, rdi                                      #10.60
        mov       QWORD PTR [64+rsp], rdx                       #315.37
        mov       QWORD PTR [72+rsp], rax                       #315.37
        mov       QWORD PTR [80+rsp], rbp                       #315.37
        mov       QWORD PTR [88+rsp], rsi                       #315.37
        vmovups   XMMWORD PTR [rsp], xmm0                       #317.20
        vmovups   XMMWORD PTR [16+rsp], xmm0                    #317.20
        mov       r9, QWORD PTR [96+rsp]                        #317.66[spill]
        mov       r14, -1                                       #81.33
        mov       QWORD PTR [128+rsp], rsi                      #[spill]
        mov       QWORD PTR [120+rsp], rbp                      #[spill]
        vpxor     xmm0, xmm0, xmm0                              #319.21
        mov       rdi, QWORD PTR [24+r9]                        #317.66
        mov       r8, QWORD PTR [16+r9]                         #317.73
        mov       rsi, QWORD PTR [8+r9]                         #317.80
        mov       r11, QWORD PTR [r9]                           #317.87
        xor       r9d, r9d                                      #77.32
        mulx      r10, r12, r11                                 #73.33
        mulx      rbx, rbp, rsi                                 #74.33
        adcx      r12, rbx                                      #77.32
        mov       rbx, 0x0ffffffff                              #82.33
        mov       QWORD PTR [200+rsp], rsi                      #317.80[spill]
        mulx      rcx, rsi, r8                                  #75.33
        adcx      rbp, rcx                                      #78.32
        mov       rcx, 0xffffffff00000001                       #83.33
        mov       QWORD PTR [192+rsp], r8                       #317.73[spill]
        mulx      r8, r15, rdi                                  #76.33
        mov       rdx, r10                                      #81.33
        adcx      rsi, r8                                       #79.32
        mov       r8d, 0                                        #79.32
        mov       QWORD PTR [184+rsp], rdi                      #317.66[spill]
        mov       edi, r8d                                      #80.30
        setb      r9b                                           #79.32
        adox      edi, r8d                                      #80.30
        mov       edi, r8d                                      #80.30
        adox      r9, r15                                       #80.30
        mulx      r14, r13, r14                                 #81.33
        seto      dil                                           #80.30
        clc                                                     #84.32
        mulx      rdi, r15, rbx                                 #82.33
        adcx      r13, rdi                                      #84.32
        mov       edi, 0                                        #85.32
        mulx      rcx, rbx, rcx                                 #83.33
        mov       edx, r8d                                      #87.30
        adcx      r15, rdi                                      #85.32
        mov       QWORD PTR [208+rsp], r11                      #317.87[spill]
        adcx      rcx, rdi                                      #86.32
        mov       edi, r8d                                      #86.32
        setb      dil                                           #86.32
        adox      edx, r8d                                      #87.30
        mov       rdx, rax                                      #93.33
        adox      rdi, rbx                                      #87.30
        mov       eax, r8d                                      #97.32
        clc                                                     #88.30
        adcx      r10, r14                                      #88.30
        adcx      r12, r13                                      #89.32
        mulx      r10, r13, QWORD PTR [192+rsp]                 #95.33[spill]
        adcx      rbp, r15                                      #90.32
        adcx      rsi, rcx                                      #91.32
        mulx      r14, rcx, r11                                 #93.33
        adcx      r9, rdi                                       #92.32
        mov       edi, r8d                                      #92.32
        mulx      r15, r11, QWORD PTR [200+rsp]                 #94.33[spill]
        setb      dil                                           #92.32
        adox      eax, r8d                                      #97.32
        mulx      rdx, rbx, QWORD PTR [184+rsp]                 #96.33[spill]
        adox      rcx, r15                                      #97.32
        mov       r15d, r8d                                     #99.32
        adox      r11, r10                                      #98.32
        mov       r10d, r8d                                     #101.34
        adox      r13, rdx                                      #99.32
        seto      r15b                                          #99.32
        clc                                                     #100.30
        adcx      r15, rbx                                      #100.30
        adox      r10d, r8d                                     #101.34
        mov       ebx, r8d                                      #105.34
        adox      r12, r14                                      #101.34
        mov       rdx, r12                                      #106.35
        adox      rbp, rcx                                      #102.34
        mov       rcx, 0x0ffffffff                              #107.35
        mulx      r14, rax, rcx                                 #107.35
        adox      rsi, r11                                      #103.34
        mov       r11, -1                                       #106.35
        adox      r9, r13                                       #104.34
        adox      rdi, r15                                      #105.34
        mulx      r15, r10, r11                                 #106.35
        mov       r11, 0xffffffff00000001                       #108.35
        seto      bl                                            #105.34
        clc                                                     #109.34
        mulx      rcx, r13, r11                                 #108.35
        mov       r11d, r8d                                     #112.31
        adcx      r10, r14                                      #109.34
        mov       r14d, 0                                       #110.34
        mov       rdx, QWORD PTR [120+rsp]                      #119.35[spill]
        adcx      rax, r14                                      #110.34
        adcx      rcx, r14                                      #111.34
        mov       r14d, r8d                                     #111.34
        setb      r14b                                          #111.34
        adox      r11d, r8d                                     #112.31
        adox      r14, r13                                      #112.31
        clc                                                     #113.31
        mov       r13d, r8d                                     #123.34
        adcx      r12, r15                                      #113.31
        mov       r12d, r8d                                     #117.34
        adcx      rbp, r10                                      #114.34
        mulx      r15, r11, QWORD PTR [192+rsp]                 #121.35[spill]
        adcx      rsi, rax                                      #115.34
        adcx      r9, rcx                                       #116.34
        adcx      rdi, r14                                      #117.34
        mulx      rax, r14, QWORD PTR [200+rsp]                 #120.35[spill]
        setb      r12b                                          #117.34
        adox      r13d, r8d                                     #123.34
        mov       DWORD PTR [136+rsp], r12d                     #117.34[spill]
        mulx      r10, r12, QWORD PTR [208+rsp]                 #119.35[spill]
        adox      r12, rax                                      #123.34
        mov       eax, r8d                                      #125.34
        mulx      rdx, rcx, QWORD PTR [184+rsp]                 #122.35[spill]
        adox      r14, r15                                      #124.34
        mov       r15d, r8d                                     #127.34
        adox      r11, rdx                                      #125.34
        seto      al                                            #125.34
        clc                                                     #126.31
        adcx      rax, rcx                                      #126.31
        adox      r15d, r8d                                     #127.34
        adox      rbp, r10                                      #127.34
        mov       r10d, r8d                                     #130.34
        mov       rdx, rbp                                      #132.35
        adox      rsi, r12                                      #128.34
        mov       r12, 0x0ffffffff                              #133.35
        adox      r9, r14                                       #129.34
        adox      rdi, r11                                      #130.34
        mov       r11, 0xffffffff00000001                       #134.35
        seto      r10b                                          #130.34
        xor       ecx, ecx                                      #130.34
        add       ebx, DWORD PTR [136+rsp]                      #131.34[spill]
        cmp       r8d, r10d                                     #131.34
        mulx      r10, r15, r12                                 #133.35
        adcx      rbx, rax                                      #131.34
        mov       rax, -1                                       #132.35
        mulx      r14, r13, rax                                 #132.35
        mulx      r12, r11, r11                                 #134.35
        mov       edx, r8d                                      #135.34
        setb      cl                                            #131.34
        adox      edx, r8d                                      #135.34
        mov       rdx, QWORD PTR [128+rsp]                      #145.35[spill]
        adox      r13, r10                                      #135.34
        mov       r10d, 0                                       #136.34
        adox      r15, r10                                      #136.34
        adox      r12, r10                                      #137.34
        mov       r10d, r8d                                     #137.34
        seto      r10b                                          #137.34
        clc                                                     #138.31
        adcx      r10, r11                                      #138.31
        mov       r11d, r8d                                     #139.31
        adox      r11d, r8d                                     #139.31
        adox      rbp, r14                                      #139.31
        adox      rsi, r13                                      #140.34
        mov       r13d, r8d                                     #143.34
        adox      r9, r15                                       #141.34
        mulx      rbp, r15, QWORD PTR [200+rsp]                 #146.35[spill]
        adox      rdi, r12                                      #142.34
        mulx      r12, r11, QWORD PTR [208+rsp]                 #145.35[spill]
        adox      rbx, r10                                      #143.34
        seto      r13b                                          #143.34
        clc                                                     #149.34
        adcx      r11, rbp                                      #149.34
        mulx      rbp, r14, QWORD PTR [192+rsp]                 #147.35[spill]
        adcx      r15, rbp                                      #150.34
        mulx      rbp, r10, QWORD PTR [184+rsp]                 #148.35[spill]
        mov       edx, r8d                                      #152.31
        adcx      r14, rbp                                      #151.34
        mov       ebp, r8d                                      #151.34
        setb      bpl                                           #151.34
        adox      edx, r8d                                      #152.31
        adox      rbp, r10                                      #152.31
        clc                                                     #153.34
        adcx      rsi, r12                                      #153.34
        mov       rdx, rsi                                      #158.35
        adcx      r9, r11                                       #154.34
        adcx      rdi, r15                                      #155.34
        mov       r15, 0x0ffffffff                              #159.35
        mulx      r15, r11, r15                                 #159.35
        adcx      rbx, r14                                      #156.34
        mov       r14d, r8d                                     #156.34
        setb      r14b                                          #156.34
        xor       r10d, r10d                                    #156.34
        add       ecx, r13d                                     #157.34
        cmp       r8d, r14d                                     #157.34
        mov       r13, 0xffffffff00000001                       #160.35
        mulx      r14, r12, rax                                 #158.35
        adcx      rcx, rbp                                      #157.34
        mulx      rbp, r13, r13                                 #160.35
        mov       edx, r8d                                      #161.34
        setb      r10b                                          #157.34
        adox      edx, r8d                                      #161.34
        mov       edx, r8d                                      #163.34
        adox      r12, r15                                      #161.34
        mov       r15d, 0                                       #162.34
        adox      r11, r15                                      #162.34
        adox      rbp, r15                                      #163.34
        seto      dl                                            #163.34
        clc                                                     #164.31
        adcx      rdx, r13                                      #164.31
        mov       r13d, r8d                                     #165.31
        adox      r13d, r8d                                     #165.31
        adox      rsi, r14                                      #165.31
        mov       esi, r8d                                      #169.34
        adox      r9, r12                                       #166.34
        adox      rdi, r11                                      #167.34
        mov       r11, 0xffffffff00000001                       #174.34
        adox      rbx, rbp                                      #168.34
        mov       rbp, rdi                                      #172.34
        adox      rcx, rdx                                      #169.34
        mov       rdx, rcx                                      #174.34
        seto      sil                                           #169.34
        xor       r12d, r12d                                    #169.34
        add       r10d, esi                                     #175.31
        mov       rsi, r9                                       #171.34
        sub       rsi, rax                                      #171.34
        mov       rax, 0x0ffffffff                              #172.34
        sbb       rbp, rax                                      #172.34
        mov       rax, rbx                                      #173.34
        sbb       rax, r15                                      #173.34
        sbb       rdx, r11                                      #174.34
        setb      r12b                                          #174.34
        cmp       r8d, r12d                                     #175.31
        sbb       r10, r15                                      #175.31
        setb      r8b                                           #175.31
        dec       r8                                            #9.35
        and       rdx, r8                                       #10.31
        and       rax, r8                                       #10.31
        and       rbp, r8                                       #10.31
        and       rsi, r8                                       #10.31
        not       r8                                            #10.43
        and       rcx, r8                                       #10.60
        and       rbx, r8                                       #10.60
        and       rdi, r8                                       #10.60
        and       r8, r9                                        #10.60
        or        rdx, rcx                                      #10.60
        or        rax, rbx                                      #10.60
        or        rbp, rdi                                      #10.60
        or        rsi, r8                                       #10.60
        mov       QWORD PTR [64+rsp], rdx                       #317.34
        mov       QWORD PTR [72+rsp], rax                       #317.34
        mov       QWORD PTR [80+rsp], rbp                       #317.34
        mov       QWORD PTR [88+rsp], rsi                       #317.34
        vmovups   XMMWORD PTR [32+rsp], xmm0                    #319.21
        vmovups   XMMWORD PTR [48+rsp], xmm0                    #319.21
        mov       QWORD PTR [128+rsp], rsi                      #[spill]
        mov       r15, -1                                       #81.33
        xor       r9d, r9d                                      #77.32
        mov       r11, QWORD PTR [152+rsp]                      #73.33[spill]
        vpxor     xmm0, xmm0, xmm0                              #320.19
        mulx      r8, rsi, QWORD PTR [176+rsp]                  #74.33[spill]
        mulx      r10, r12, r11                                 #73.33
        adcx      r12, r8                                       #77.32
        mov       r8d, 0                                        #79.32
        mov       QWORD PTR [120+rsp], rbp                      #[spill]
        mulx      rbp, rdi, QWORD PTR [168+rsp]                 #75.33[spill]
        adcx      rsi, rbp                                      #78.32
        mov       ebp, r8d                                      #80.30
        mulx      rcx, rbx, QWORD PTR [160+rsp]                 #76.33[spill]
        mov       rdx, r10                                      #81.33
        adcx      rdi, rcx                                      #79.32
        mov       rcx, 0xffffffff00000001                       #83.33
        mulx      r14, r13, r15                                 #81.33
        setb      r9b                                           #79.32
        adox      ebp, r8d                                      #80.30
        adox      r9, rbx                                       #80.30
        mulx      rbx, rcx, rcx                                 #83.33
        mov       rbp, 0x0ffffffff                              #82.33
        clc                                                     #84.32
        mulx      rbp, r15, rbp                                 #82.33
        mov       edx, r8d                                      #87.30
        adcx      r13, rbp                                      #84.32
        mov       ebp, 0                                        #85.32
        adcx      r15, rbp                                      #85.32
        adcx      rbx, rbp                                      #86.32
        mov       ebp, r8d                                      #86.32
        setb      bpl                                           #86.32
        adox      edx, r8d                                      #87.30
        mov       rdx, rax                                      #93.33
        adox      rbp, rcx                                      #87.30
        mov       eax, r8d                                      #97.32
        clc                                                     #88.30
        adcx      r10, r14                                      #88.30
        adcx      r12, r13                                      #89.32
        adcx      rsi, r15                                      #90.32
        mulx      r15, r13, QWORD PTR [168+rsp]                 #95.33[spill]
        adcx      rdi, rbx                                      #91.32
        mulx      r10, rbx, r11                                 #93.33
        adcx      r9, rbp                                       #92.32
        mov       ebp, r8d                                      #92.32
        mulx      r11, r14, QWORD PTR [176+rsp]                 #94.33[spill]
        setb      bpl                                           #92.32
        adox      eax, r8d                                      #97.32
        mulx      rdx, rcx, QWORD PTR [160+rsp]                 #96.33[spill]
        adox      rbx, r11                                      #97.32
        mov       r11d, r8d                                     #99.32
        adox      r14, r15                                      #98.32
        mov       r15d, r8d                                     #101.34
        adox      r13, rdx                                      #99.32
        seto      r11b                                          #99.32
        clc                                                     #100.30
        adcx      r11, rcx                                      #100.30
        adox      r15d, r8d                                     #101.34
        mov       ecx, r8d                                      #105.34
        adox      r12, r10                                      #101.34
        mov       r10, -1                                       #106.35
        mov       rdx, r12                                      #106.35
        adox      rsi, rbx                                      #102.34
        mov       rbx, 0x0ffffffff                              #107.35
        adox      rdi, r14                                      #103.34
        mulx      r14, rax, rbx                                 #107.35
        adox      r9, r13                                       #104.34
        adox      rbp, r11                                      #105.34
        mulx      r11, r15, r10                                 #106.35
        mov       r10, 0xffffffff00000001                       #108.35
        seto      cl                                            #105.34
        clc                                                     #109.34
        mulx      rbx, r13, r10                                 #108.35
        mov       r10d, r8d                                     #111.34
        adcx      r15, r14                                      #109.34
        mov       r14d, 0                                       #110.34
        mov       rdx, QWORD PTR [120+rsp]                      #119.35[spill]
        adcx      rax, r14                                      #110.34
        adcx      rbx, r14                                      #111.34
        mov       r14d, r8d                                     #112.31
        setb      r10b                                          #111.34
        adox      r14d, r8d                                     #112.31
        adox      r10, r13                                      #112.31
        clc                                                     #113.31
        mov       r13d, r8d                                     #123.34
        adcx      r12, r11                                      #113.31
        mov       r12d, r8d                                     #117.34
        adcx      rsi, r15                                      #114.34
        mulx      r11, r14, QWORD PTR [168+rsp]                 #121.35[spill]
        adcx      rdi, rax                                      #115.34
        adcx      r9, rbx                                       #116.34
        adcx      rbp, r10                                      #117.34
        mulx      r15, r10, QWORD PTR [152+rsp]                 #119.35[spill]
        setb      r12b                                          #117.34
        adox      r13d, r8d                                     #123.34
        mov       DWORD PTR [136+rsp], r12d                     #117.34[spill]
        mulx      rbx, r12, QWORD PTR [176+rsp]                 #120.35[spill]
        adox      r10, rbx                                      #123.34
        mov       ebx, r8d                                      #125.34
        mulx      rdx, rax, QWORD PTR [160+rsp]                 #122.35[spill]
        adox      r12, r11                                      #124.34
        mov       r11d, r8d                                     #127.34
        adox      r14, rdx                                      #125.34
        seto      bl                                            #125.34
        clc                                                     #126.31
        adcx      rbx, rax                                      #126.31
        adox      r11d, r8d                                     #127.34
        adox      rsi, r15                                      #127.34
        mov       r15d, r8d                                     #130.34
        mov       rdx, rsi                                      #132.35
        adox      rdi, r10                                      #128.34
        mov       r10, 0x0ffffffff                              #133.35
        adox      r9, r12                                       #129.34
        mov       r12, 0xffffffff00000001                       #134.35
        adox      rbp, r14                                      #130.34
        seto      r15b                                          #130.34
        xor       eax, eax                                      #130.34
        add       ecx, DWORD PTR [136+rsp]                      #131.34[spill]
        cmp       r8d, r15d                                     #131.34
        mulx      r11, r15, r10                                 #133.35
        adcx      rcx, rbx                                      #131.34
        mov       rbx, -1                                       #132.35
        mulx      r14, r13, rbx                                 #132.35
        mulx      r10, r12, r12                                 #134.35
        mov       edx, r8d                                      #135.34
        setb      al                                            #131.34
        adox      edx, r8d                                      #135.34
        mov       rdx, QWORD PTR [128+rsp]                      #145.35[spill]
        adox      r13, r11                                      #135.34
        mov       r11d, 0                                       #136.34
        adox      r15, r11                                      #136.34
        adox      r10, r11                                      #137.34
        mov       r11d, r8d                                     #137.34
        seto      r11b                                          #137.34
        clc                                                     #138.31
        adcx      r11, r12                                      #138.31
        mov       r12d, r8d                                     #139.31
        adox      r12d, r8d                                     #139.31
        adox      rsi, r14                                      #139.31
        mulx      r12, rsi, QWORD PTR [152+rsp]                 #145.35[spill]
        adox      rdi, r13                                      #140.34
        mov       r13d, r8d                                     #143.34
        adox      r9, r15                                       #141.34
        mulx      r14, r15, QWORD PTR [176+rsp]                 #146.35[spill]
        adox      rbp, r10                                      #142.34
        adox      rcx, r11                                      #143.34
        seto      r13b                                          #143.34
        clc                                                     #149.34
        adcx      rsi, r14                                      #149.34
        mulx      r10, r14, QWORD PTR [168+rsp]                 #147.35[spill]
        adcx      r15, r10                                      #150.34
        mulx      r11, r10, QWORD PTR [160+rsp]                 #148.35[spill]
        mov       edx, r8d                                      #152.31
        adcx      r14, r11                                      #151.34
        mov       r11d, r8d                                     #151.34
        setb      r11b                                          #151.34
        adox      edx, r8d                                      #152.31
        adox      r11, r10                                      #152.31
        clc                                                     #153.34
        adcx      rdi, r12                                      #153.34
        mov       rdx, rdi                                      #158.35
        adcx      r9, rsi                                       #154.34
        mov       esi, r8d                                      #156.34
        adcx      rbp, r15                                      #155.34
        adcx      rcx, r14                                      #156.34
        mulx      r14, r12, rbx                                 #158.35
        setb      sil                                           #156.34
        xor       r10d, r10d                                    #156.34
        add       eax, r13d                                     #157.34
        cmp       r8d, esi                                      #157.34
        mov       rsi, 0xffffffff00000001                       #160.35
        mulx      rsi, r13, rsi                                 #160.35
        adcx      rax, r11                                      #157.34
        mov       r11, 0x0ffffffff                              #159.35
        mulx      r15, r11, r11                                 #159.35
        mov       edx, r8d                                      #161.34
        setb      r10b                                          #157.34
        adox      edx, r8d                                      #161.34
        mov       edx, r8d                                      #163.34
        adox      r12, r15                                      #161.34
        mov       r15d, 0                                       #162.34
        adox      r11, r15                                      #162.34
        adox      rsi, r15                                      #163.34
        seto      dl                                            #163.34
        clc                                                     #164.31
        adcx      rdx, r13                                      #164.31
        mov       r13d, r8d                                     #165.31
        adox      r13d, r8d                                     #165.31
        adox      rdi, r14                                      #165.31
        mov       r14, 0xffffffff00000001                       #174.34
        mov       edi, r8d                                      #169.34
        adox      r9, r12                                       #166.34
        mov       r12, 0x0ffffffff                              #172.34
        adox      rbp, r11                                      #167.34
        adox      rcx, rsi                                      #168.34
        mov       r11, rcx                                      #173.34
        adox      rax, rdx                                      #169.34
        mov       rsi, rax                                      #174.34
        seto      dil                                           #169.34
        add       r10d, edi                                     #175.31
        mov       rdi, r9                                       #171.34
        sub       rdi, rbx                                      #171.34
        mov       rbx, rbp                                      #172.34
        sbb       rbx, r12                                      #172.34
        sbb       r11, r15                                      #173.34
        sbb       rsi, r14                                      #174.34
        mov       r14d, r8d                                     #174.34
        setb      r14b                                          #174.34
        cmp       r8d, r14d                                     #175.31
        sbb       r10, r15                                      #175.31
        setb      r8b                                           #175.31
        dec       r8                                            #9.35
        and       rsi, r8                                       #10.31
        and       r11, r8                                       #10.31
        and       rbx, r8                                       #10.31
        and       rdi, r8                                       #10.31
        not       r8                                            #10.43
        and       rax, r8                                       #10.60
        and       rcx, r8                                       #10.60
        and       rbp, r8                                       #10.60
        and       r8, r9                                        #10.60
        or        rsi, rax                                      #10.60
        or        r11, rcx                                      #10.60
        or        rbx, rbp                                      #10.60
        or        rdi, r8                                       #10.60
        mov       QWORD PTR [216+rsp], rsi                      #10.60[spill]
        mov       QWORD PTR [32+rsp], rsi                       #319.35
        mov       QWORD PTR [40+rsp], r11                       #319.35
        mov       QWORD PTR [224+rsp], rdi                      #10.60[spill]
        mov       QWORD PTR [48+rsp], rbx                       #319.35
        mov       QWORD PTR [56+rsp], rdi                       #319.35
        vmovups   XMMWORD PTR [64+rsp], xmm0                    #320.19
        vmovups   XMMWORD PTR [80+rsp], xmm0                    #320.19
        mov       r8, QWORD PTR [112+rsp]                       #41.32[spill]
        xor       ebp, ebp                                      #41.32
        mov       r14, QWORD PTR [rsp]                          #41.32
        xor       edi, edi                                      #44.32
        mov       rsi, QWORD PTR [8+rsp]                        #42.32
        xor       r9d, r9d                                      #48.32
        sub       r14, QWORD PTR [r8]                           #41.32
        mov       r12, 0xffffffff00000001                       #49.30
        mov       rcx, QWORD PTR [16+rsp]                       #43.32
        sbb       rsi, QWORD PTR [8+r8]                         #42.32
        mov       r10, QWORD PTR [24+rsp]                       #44.32
        vpxor     xmm0, xmm0, xmm0                              #323.20
        sbb       rcx, QWORD PTR [16+r8]                        #43.32
        mov       QWORD PTR [120+rsp], r11                      #[spill]
        sbb       r10, QWORD PTR [24+r8]                        #44.32
        setb      dil                                           #44.32
        xor       r13d, r13d                                    #44.32
        mov       r11, -1                                       #44.32
        xor       r8d, r8d                                      #44.32
        xor       edx, edx                                      #44.32
        test      edi, edi                                      #45.38
        mov       QWORD PTR [232+rsp], rbx                      #[spill]
        cmovne    rdx, r11                                      #45.38
        clc                                                     #46.32
        mov       eax, edx                                      #47.32
        adcx      r14, rdx                                      #46.32
        mov       QWORD PTR [288+rsp], r14                      #46.32[spill]
        adcx      rsi, rax                                      #47.32
        mov       QWORD PTR [296+rsp], rsi                      #47.32[spill]
        adcx      rcx, r8                                       #48.32
        mov       QWORD PTR [80+rsp], rsi                       #320.33
        setb      r9b                                           #48.32
        and       rdx, r12                                      #49.30
        cmp       ebp, r9d                                      #49.30
        mov       QWORD PTR [88+rsp], r14                       #320.33
        adcx      r10, rdx                                      #49.30
        mov       rdx, QWORD PTR [152+rsp]                      #73.33[spill]
        adox      r13d, ebp                                     #77.32
        mulx      rax, rbx, r10                                 #73.33
        mulx      r15, r9, rcx                                  #74.33
        adox      rbx, r15                                      #77.32
        mulx      rdi, rsi, rsi                                 #75.33
        adox      r9, rdi                                       #78.32
        mov       edi, ebp                                      #79.32
        mov       QWORD PTR [304+rsp], rcx                      #48.32[spill]
        mov       QWORD PTR [72+rsp], rcx                       #320.33
        mulx      r14, rcx, r14                                 #76.33
        mov       rdx, rax                                      #81.33
        adox      rsi, r14                                      #79.32
        mulx      r14, r15, r11                                 #81.33
        mov       r11, 0x0ffffffff                              #82.33
        seto      dil                                           #79.32
        clc                                                     #80.30
        adcx      rdi, rcx                                      #80.30
        mov       QWORD PTR [280+rsp], r10                      #49.30[spill]
        mulx      r13, rcx, r11                                 #82.33
        mov       r11d, ebp                                     #84.32
        adox      r11d, ebp                                     #84.32
        mulx      r12, rdx, r12                                 #83.33
        mov       r11d, ebp                                     #86.32
        adox      r15, r13                                      #84.32
        mov       QWORD PTR [64+rsp], r10                       #320.33
        adox      rcx, r8                                       #85.32
        adox      r12, r8                                       #86.32
        seto      r11b                                          #86.32
        clc                                                     #87.30
        adcx      r11, rdx                                      #87.30
        mov       rdx, QWORD PTR [176+rsp]                      #93.33[spill]
        mov       r13d, ebp                                     #88.30
        adox      r13d, ebp                                     #88.30
        adox      rax, r14                                      #88.30
        mulx      r14, r13, r10                                 #93.33
        adox      rbx, r15                                      #89.32
        adox      r9, rcx                                       #90.32
        mov       ecx, ebp                                      #92.32
        adox      rsi, r12                                      #91.32
        mulx      rax, r12, QWORD PTR [304+rsp]                 #94.33[spill]
        adox      rdi, r11                                      #92.32
        seto      cl                                            #92.32
        clc                                                     #97.32
        adcx      r13, rax                                      #97.32
        mulx      rax, r15, QWORD PTR [296+rsp]                 #95.33[spill]
        adcx      r12, rax                                      #98.32
        mulx      rax, r11, QWORD PTR [288+rsp]                 #96.33[spill]
        mov       edx, ebp                                      #100.30
        adcx      r15, rax                                      #99.32
        mov       eax, ebp                                      #99.32
        setb      al                                            #99.32
        adox      edx, ebp                                      #100.30
        adox      rax, r11                                      #100.30
        mov       r11d, ebp                                     #100.30
        seto      r11b                                          #100.30
        clc                                                     #101.34
        adcx      rbx, r14                                      #101.34
        mov       rdx, rbx                                      #106.35
        adcx      r9, r13                                       #102.34
        adcx      rsi, r12                                      #103.34
        mov       r12d, ebp                                     #105.34
        adcx      rdi, r15                                      #104.34
        mov       r15, -1                                       #106.35
        mulx      r15, r14, r15                                 #106.35
        adcx      rcx, rax                                      #105.34
        mov       rax, 0x0ffffffff                              #107.35
        mulx      r11, r13, rax                                 #107.35
        setb      r12b                                          #105.34
        mov       DWORD PTR [128+rsp], r12d                     #105.34[spill]
        mov       r12, 0xffffffff00000001                       #108.35
        mulx      rax, r12, r12                                 #108.35
        mov       edx, ebp                                      #109.34
        adox      edx, ebp                                      #109.34
        mov       rdx, QWORD PTR [168+rsp]                      #119.35[spill]
        adox      r14, r11                                      #109.34
        mov       r11d, ebp                                     #111.34
        adox      r13, r8                                       #110.34
        adox      rax, r8                                       #111.34
        seto      r11b                                          #111.34
        clc                                                     #112.31
        adcx      r11, r12                                      #112.31
        mov       r12d, ebp                                     #113.31
        adox      r12d, ebp                                     #113.31
        adox      rbx, r15                                      #113.31
        mulx      rbx, r15, r10                                 #119.35
        adox      r9, r14                                       #114.34
        mov       r14d, ebp                                     #117.34
        adox      rsi, r13                                      #115.34
        adox      rdi, rax                                      #116.34
        mulx      rax, r13, QWORD PTR [304+rsp]                 #120.35[spill]
        adox      rcx, r11                                      #117.34
        mulx      r11, r12, QWORD PTR [296+rsp]                 #121.35[spill]
        seto      r14b                                          #117.34
        clc                                                     #123.34
        adcx      r15, rax                                      #123.34
        adcx      r13, r11                                      #124.34
        mulx      r11, rax, QWORD PTR [288+rsp]                 #122.35[spill]
        mov       edx, ebp                                      #126.31
        adcx      r12, r11                                      #125.34
        mov       r11d, ebp                                     #125.34
        setb      r11b                                          #125.34
        adox      edx, ebp                                      #126.31
        adox      r11, rax                                      #126.31
        clc                                                     #127.34
        mov       eax, DWORD PTR [128+rsp]                      #131.34[spill]
        adcx      r9, rbx                                       #127.34
        mov       ebx, ebp                                      #130.34
        mov       rdx, r9                                       #132.35
        adcx      rsi, r15                                      #128.34
        mov       r15, 0x0ffffffff                              #133.35
        adcx      rdi, r13                                      #129.34
        adcx      rcx, r12                                      #130.34
        setb      bl                                            #130.34
        add       eax, r14d                                     #131.34
        xor       r14d, r14d                                    #131.34
        cmp       ebp, ebx                                      #131.34
        adcx      rax, r11                                      #131.34
        mov       r11, -1                                       #132.35
        mulx      r12, rbx, r11                                 #132.35
        setb      r14b                                          #131.34
        mov       DWORD PTR [136+rsp], r14d                     #131.34[spill]
        mov       r14, 0xffffffff00000001                       #134.35
        mulx      r15, r11, r15                                 #133.35
        mulx      r14, r13, r14                                 #134.35
        mov       edx, ebp                                      #135.34
        adox      edx, ebp                                      #135.34
        mov       rdx, QWORD PTR [160+rsp]                      #145.35[spill]
        adox      rbx, r15                                      #135.34
        mov       r15d, ebp                                     #137.34
        adox      r11, r8                                       #136.34
        adox      r14, r8                                       #137.34
        seto      r15b                                          #137.34
        clc                                                     #138.31
        adcx      r15, r13                                      #138.31
        mov       r13d, ebp                                     #139.31
        adox      r13d, ebp                                     #139.31
        mov       r13d, ebp                                     #152.31
        adox      r9, r12                                       #139.31
        adox      rsi, rbx                                      #140.34
        mulx      r10, rbx, r10                                 #145.35
        adox      rdi, r11                                      #141.34
        adox      rcx, r14                                      #142.34
        mov       r14d, ebp                                     #143.34
        adox      rax, r15                                      #143.34
        mulx      r9, r15, QWORD PTR [304+rsp]                  #146.35[spill]
        seto      r14b                                          #143.34
        clc                                                     #149.34
        adcx      rbx, r9                                       #149.34
        mulx      r11, r9, QWORD PTR [296+rsp]                  #147.35[spill]
        adcx      r15, r11                                      #150.34
        mulx      r12, r11, QWORD PTR [288+rsp]                 #148.35[spill]
        adcx      r9, r12                                       #151.34
        mov       r12d, ebp                                     #151.34
        setb      r12b                                          #151.34
        adox      r13d, ebp                                     #152.31
        adox      r12, r11                                      #152.31
        clc                                                     #153.34
        mov       r11d, DWORD PTR [136+rsp]                     #157.34[spill]
        adcx      rsi, r10                                      #153.34
        mov       r10d, ebp                                     #156.34
        mov       rdx, rsi                                      #158.35
        adcx      rdi, rbx                                      #154.34
        mov       rbx, 0x0ffffffff                              #159.35
        adcx      rcx, r15                                      #155.34
        mov       r15, 0xffffffff00000001                       #160.35
        mulx      r15, r13, r15                                 #160.35
        adcx      rax, r9                                       #156.34
        setb      r10b                                          #156.34
        mov       r9, -1                                        #156.34
        add       r11d, r14d                                    #157.34
        cmp       ebp, r10d                                     #157.34
        mulx      r9, r10, r9                                   #158.35
        adcx      r11, r12                                      #157.34
        mov       r12d, ebp                                     #157.34
        mulx      r14, rbx, rbx                                 #159.35
        mov       edx, ebp                                      #161.34
        setb      r12b                                          #157.34
        adox      edx, ebp                                      #161.34
        mov       rdx, 0x0ffffffff                              #172.34
        adox      r10, r14                                      #161.34
        mov       r14d, ebp                                     #163.34
        adox      rbx, r8                                       #162.34
        adox      r15, r8                                       #163.34
        seto      r14b                                          #163.34
        clc                                                     #164.31
        adcx      r14, r13                                      #164.31
        mov       r13d, ebp                                     #165.31
        adox      r13d, ebp                                     #165.31
        adox      rsi, r9                                       #165.31
        mov       esi, ebp                                      #169.34
        adox      rdi, r10                                      #166.34
        mov       r9, rdi                                       #171.34
        adox      rcx, rbx                                      #167.34
        mov       rbx, 0xffffffff00000001                       #174.34
        adox      rax, r15                                      #168.34
        adox      r11, r14                                      #169.34
        seto      sil                                           #169.34
        mov       r10, -1                                       #169.34
        xor       r15d, r15d                                    #169.34
        add       r12d, esi                                     #175.31
        sub       r9, r10                                       #171.34
        mov       r10, rcx                                      #172.34
        mov       rsi, r11                                      #174.34
        sbb       r10, rdx                                      #172.34
        mov       rdx, rax                                      #173.34
        sbb       rdx, r8                                       #173.34
        sbb       rsi, rbx                                      #174.34
        mov       rbx, QWORD PTR [104+rsp]                      #180.1[spill]
        setb      r15b                                          #174.34
        cmp       ebp, r15d                                     #175.31
        sbb       r12, r8                                       #175.31
        setb      bpl                                           #175.31
        dec       rbp                                           #9.35
        and       rsi, rbp                                      #10.31
        and       rdx, rbp                                      #10.31
        and       r10, rbp                                      #10.31
        and       r9, rbp                                       #10.31
        not       rbp                                           #10.43
        and       r11, rbp                                      #10.60
        and       rax, rbp                                      #10.60
        or        rsi, r11                                      #10.60
        and       rcx, rbp                                      #10.60
        mov       QWORD PTR [64+rbx], rsi                       #180.1
        and       rbp, rdi                                      #10.60
        mov       rsi, QWORD PTR [96+rsp]                       #322.60[spill]
        or        rdx, rax                                      #10.60
        or        r10, rcx                                      #10.60
        or        r9, rbp                                       #10.60
        mov       QWORD PTR [72+rbx], rdx                       #181.1
        mov       QWORD PTR [80+rbx], r10                       #182.1
        mov       QWORD PTR [88+rbx], r9                        #183.1
        mov       rax, QWORD PTR [32+rsi]                       #322.60
        mov       rdx, QWORD PTR [40+rsi]                       #322.53
        mov       rcx, QWORD PTR [48+rsi]                       #322.46
        mov       rdi, QWORD PTR [56+rsi]                       #322.39
        mov       QWORD PTR [272+rsp], rax                      #322.60[spill]
        mov       QWORD PTR [264+rsp], rdx                      #322.53[spill]
        mov       QWORD PTR [256+rsp], rcx                      #322.46[spill]
        mov       QWORD PTR [248+rsp], rdi                      #322.39[spill]
        vmovups   XMMWORD PTR [32+rsp], xmm0                    #323.20
        vmovups   XMMWORD PTR [48+rsp], xmm0                    #323.20
        mov       rbx, QWORD PTR [232+rsp]                      #323.20[spill]
        mov       r11, QWORD PTR [120+rsp]                      #323.20[spill]
        mov       rdx, QWORD PTR [216+rsp]                      #73.33[spill]
        xor       ecx, ecx                                      #77.32
        xor       r12d, r12d                                    #77.32
        xor       esi, esi                                      #77.32
        vpxor     xmm0, xmm0, xmm0                              #324.19
        mov       r9, rax                                       #73.33
        mov       QWORD PTR [232+rsp], rbx                      #[spill]
        mulx      r15, r10, r9                                  #73.33
        mulx      r8, rbx, QWORD PTR [264+rsp]                  #74.33[spill]
        adcx      r10, r8                                       #77.32
        mov       r8d, 0                                        #79.32
        mulx      rbp, rdi, QWORD PTR [256+rsp]                 #75.33[spill]
        adcx      rbx, rbp                                      #78.32
        mulx      rax, r14, QWORD PTR [248+rsp]                 #76.33[spill]
        adcx      rdi, rax                                      #79.32
        mov       rbp, -1                                       #81.33
        mov       rdx, r15                                      #81.33
        mov       rax, 0xffffffff00000001                       #83.33
        setb      sil                                           #79.32
        adox      ecx, r8d                                      #80.30
        adox      rsi, r14                                      #80.30
        mulx      rcx, rax, rax                                 #83.33
        seto      r12b                                          #80.30
        mulx      r12, r13, rbp                                 #81.33
        mov       rbp, 0x0ffffffff                              #82.33
        clc                                                     #84.32
        mulx      rbp, r14, rbp                                 #82.33
        mov       edx, r8d                                      #87.30
        adcx      r13, rbp                                      #84.32
        mov       ebp, 0                                        #85.32
        adcx      r14, rbp                                      #85.32
        adcx      rcx, rbp                                      #86.32
        mov       ebp, r8d                                      #86.32
        setb      bpl                                           #86.32
        adox      edx, r8d                                      #87.30
        mov       rdx, r11                                      #93.33
        adox      rbp, rax                                      #87.30
        mov       r11d, r8d                                     #97.32
        clc                                                     #88.30
        adcx      r15, r12                                      #88.30
        adcx      r10, r13                                      #89.32
        adcx      rbx, r14                                      #90.32
        mulx      r14, r13, QWORD PTR [264+rsp]                 #94.33[spill]
        adcx      rdi, rcx                                      #91.32
        mulx      r12, rcx, r9                                  #93.33
        adcx      rsi, rbp                                      #92.32
        mov       ebp, r8d                                      #92.32
        mulx      r9, r15, QWORD PTR [256+rsp]                  #95.33[spill]
        setb      bpl                                           #92.32
        adox      r11d, r8d                                     #97.32
        mulx      rdx, rax, QWORD PTR [248+rsp]                 #96.33[spill]
        mov       r11, 0x0ffffffff                              #107.35
        adox      rcx, r14                                      #97.32
        mov       r14d, r8d                                     #99.32
        adox      r13, r9                                       #98.32
        mov       r9d, r8d                                      #101.34
        adox      r15, rdx                                      #99.32
        seto      r14b                                          #99.32
        clc                                                     #100.30
        adcx      r14, rax                                      #100.30
        adox      r9d, r8d                                      #101.34
        mov       eax, r8d                                      #105.34
        adox      r10, r12                                      #101.34
        mov       rdx, r10                                      #106.35
        adox      rbx, rcx                                      #102.34
        mov       rcx, -1                                       #106.35
        mulx      r9, r12, rcx                                  #106.35
        adox      rdi, r13                                      #103.34
        adox      rsi, r15                                      #104.34
        mov       r15, 0xffffffff00000001                       #108.35
        mulx      r15, rcx, r15                                 #108.35
        adox      rbp, r14                                      #105.34
        mulx      r13, r14, r11                                 #107.35
        mov       r11d, 0                                       #110.34
        seto      al                                            #105.34
        clc                                                     #109.34
        mov       rdx, QWORD PTR [232+rsp]                      #119.35[spill]
        adcx      r12, r13                                      #109.34
        mov       r13d, r8d                                     #112.31
        adcx      r14, r11                                      #110.34
        adcx      r15, r11                                      #111.34
        mov       r11d, r8d                                     #111.34
        setb      r11b                                          #111.34
        adox      r13d, r8d                                     #112.31
        adox      r11, rcx                                      #112.31
        mov       ecx, r8d                                      #112.31
        seto      cl                                            #112.31
        clc                                                     #113.31
        adcx      r10, r9                                       #113.31
        mov       r10d, r8d                                     #117.34
        adcx      rbx, r12                                      #114.34
        mulx      r9, r12, QWORD PTR [272+rsp]                  #119.35[spill]
        adcx      rdi, r14                                      #115.34
        adcx      rsi, r15                                      #116.34
        mov       r15d, r8d                                     #123.34
        adcx      rbp, r11                                      #117.34
        mulx      rcx, r11, QWORD PTR [264+rsp]                 #120.35[spill]
        setb      r10b                                          #117.34
        adox      r15d, r8d                                     #123.34
        mov       DWORD PTR [rsp], r10d                         #117.34[spill]
        adox      r12, rcx                                      #123.34
        mov       ecx, r8d                                      #125.34
        mulx      r10, r13, QWORD PTR [256+rsp]                 #121.35[spill]
        adox      r11, r10                                      #124.34
        mov       r10d, r8d                                     #127.34
        mulx      rdx, r14, QWORD PTR [248+rsp]                 #122.35[spill]
        adox      r13, rdx                                      #125.34
        seto      cl                                            #125.34
        clc                                                     #126.31
        adcx      rcx, r14                                      #126.31
        adox      r10d, r8d                                     #127.34
        mov       r10, 0xffffffff00000001                       #134.35
        adox      rbx, r9                                       #127.34
        mov       r9d, r8d                                      #130.34
        mov       rdx, rbx                                      #132.35
        adox      rdi, r12                                      #128.34
        mulx      r10, r15, r10                                 #134.35
        adox      rsi, r11                                      #129.34
        adox      rbp, r13                                      #130.34
        mov       r13, 0x0ffffffff                              #133.35
        seto      r9b                                           #130.34
        xor       r14d, r14d                                    #130.34
        add       eax, DWORD PTR [rsp]                          #131.34[spill]
        cmp       r8d, r9d                                      #131.34
        mulx      r9, r13, r13                                  #133.35
        adcx      rax, rcx                                      #131.34
        mov       rcx, -1                                       #132.35
        mulx      r12, r11, rcx                                 #132.35
        mov       edx, r8d                                      #135.34
        setb      r14b                                          #131.34
        adox      edx, r8d                                      #135.34
        mov       rdx, QWORD PTR [224+rsp]                      #145.35[spill]
        adox      r11, r9                                       #135.34
        mov       r9d, 0                                        #136.34
        adox      r13, r9                                       #136.34
        adox      r10, r9                                       #137.34
        mov       r9d, r8d                                      #137.34
        seto      r9b                                           #137.34
        clc                                                     #138.31
        adcx      r9, r15                                       #138.31
        mov       r15d, r8d                                     #139.31
        adox      r15d, r8d                                     #139.31
        adox      rbx, r12                                      #139.31
        adox      rdi, r11                                      #140.34
        mulx      r11, rbx, QWORD PTR [264+rsp]                 #146.35[spill]
        adox      rsi, r13                                      #141.34
        mov       r13d, r8d                                     #143.34
        adox      rbp, r10                                      #142.34
        mulx      r10, r12, QWORD PTR [272+rsp]                 #145.35[spill]
        adox      rax, r9                                       #143.34
        seto      r13b                                          #143.34
        clc                                                     #149.34
        adcx      r12, r11                                      #149.34
        mulx      r9, r11, QWORD PTR [256+rsp]                  #147.35[spill]
        adcx      rbx, r9                                       #150.34
        mulx      r9, r15, QWORD PTR [248+rsp]                  #148.35[spill]
        mov       edx, r8d                                      #152.31
        adcx      r11, r9                                       #151.34
        mov       r9d, r8d                                      #151.34
        setb      r9b                                           #151.34
        adox      edx, r8d                                      #152.31
        adox      r9, r15                                       #152.31
        clc                                                     #153.34
        mov       r15, 0xffffffff00000001                       #160.35
        adcx      rdi, r10                                      #153.34
        mov       r10, 0x0ffffffff                              #159.35
        mov       rdx, rdi                                      #158.35
        adcx      rsi, r12                                      #154.34
        adcx      rbp, rbx                                      #155.34
        mov       ebx, r8d                                      #156.34
        adcx      rax, r11                                      #156.34
        mulx      r11, r12, rcx                                 #158.35
        setb      bl                                            #156.34
        add       r14d, r13d                                    #157.34
        cmp       r8d, ebx                                      #157.34
        mulx      r10, r13, r10                                 #159.35
        adcx      r14, r9                                       #157.34
        mov       r9d, r8d                                      #157.34
        mulx      r15, rbx, r15                                 #160.35
        mov       edx, r8d                                      #161.34
        setb      r9b                                           #157.34
        adox      edx, r8d                                      #161.34
        mov       edx, r8d                                      #163.34
        adox      r12, r10                                      #161.34
        mov       r10d, 0                                       #162.34
        adox      r13, r10                                      #162.34
        adox      r15, r10                                      #163.34
        seto      dl                                            #163.34
        clc                                                     #164.31
        adcx      rdx, rbx                                      #164.31
        mov       ebx, r8d                                      #165.31
        adox      ebx, r8d                                      #165.31
        adox      rdi, r11                                      #165.31
        mov       r11, 0x0ffffffff                              #172.34
        mov       edi, r8d                                      #169.34
        adox      rsi, r12                                      #166.34
        mov       r12, 0xffffffff00000001                       #174.34
        adox      rbp, r13                                      #167.34
        adox      rax, r15                                      #168.34
        mov       rbx, rax                                      #173.34
        adox      r14, rdx                                      #169.34
        mov       rdx, r14                                      #174.34
        seto      dil                                           #169.34
        xor       r13d, r13d                                    #169.34
        add       r9d, edi                                      #175.31
        mov       rdi, rsi                                      #171.34
        sub       rdi, rcx                                      #171.34
        mov       rcx, rbp                                      #172.34
        sbb       rcx, r11                                      #172.34
        sbb       rbx, r10                                      #173.34
        sbb       rdx, r12                                      #174.34
        setb      r13b                                          #174.34
        cmp       r8d, r13d                                     #175.31
        sbb       r9, r10                                       #175.31
        setb      r8b                                           #175.31
        dec       r8                                            #9.35
        and       rdx, r8                                       #10.31
        and       rbx, r8                                       #10.31
        and       rcx, r8                                       #10.31
        and       rdi, r8                                       #10.31
        not       r8                                            #10.43
        and       r14, r8                                       #10.60
        and       rax, r8                                       #10.60
        and       rbp, r8                                       #10.60
        and       r8, rsi                                       #10.60
        or        rdx, r14                                      #10.60
        or        rbx, rax                                      #10.60
        or        rcx, rbp                                      #10.60
        or        rdi, r8                                       #10.60
        mov       QWORD PTR [120+rsp], rdx                      #10.60[spill]
        mov       QWORD PTR [32+rsp], rdx                       #323.34
        mov       QWORD PTR [136+rsp], rbx                      #10.60[spill]
        mov       QWORD PTR [40+rsp], rbx                       #323.34
        mov       QWORD PTR [128+rsp], rcx                      #10.60[spill]
        mov       QWORD PTR [144+rsp], rdi                      #10.60[spill]
        mov       QWORD PTR [48+rsp], rcx                       #323.34
        mov       QWORD PTR [56+rsp], rdi                       #323.34
        vmovups   XMMWORD PTR [64+rsp], xmm0                    #324.19
        vmovups   XMMWORD PTR [80+rsp], xmm0                    #324.19
        mov       r12, rdi                                      #44.32
        mov       rsi, rcx                                      #43.32
        mov       rax, QWORD PTR [112+rsp]                      #41.32[spill]
        xor       r11d, r11d                                    #41.32
        mov       rcx, rdx                                      #41.32
        xor       edx, edx                                      #44.32
        mov       rdi, rbx                                      #42.32
        xor       ebp, ebp                                      #45.38
        sub       rcx, QWORD PTR [32+rax]                       #41.32
        sbb       rdi, QWORD PTR [40+rax]                       #42.32
        mov       r10, 0xffffffff00000001                       #49.30
        sbb       rsi, QWORD PTR [48+rax]                       #43.32
        vpxor     xmm0, xmm0, xmm0                              #325.20
        sbb       r12, QWORD PTR [56+rax]                       #44.32
        setb      dl                                            #44.32
        mov       r8, -1                                        #44.32
        xor       r9d, r9d                                      #44.32
        test      edx, edx                                      #45.38
        cmove     r8, rbp                                       #45.38
        clc                                                     #46.32
        mov       ebx, r8d                                      #47.32
        adcx      rcx, r8                                       #46.32
        mov       QWORD PTR [120+rsp], rcx                      #46.32[spill]
        adcx      rdi, rbx                                      #47.32
        mov       QWORD PTR [88+rsp], rcx                       #324.33
        adcx      rsi, rbp                                      #48.32
        mov       QWORD PTR [136+rsp], rdi                      #47.32[spill]
        setb      r9b                                           #48.32
        and       r10, r8                                       #49.30
        cmp       r11d, r9d                                     #49.30
        mov       QWORD PTR [128+rsp], rsi                      #48.32[spill]
        adcx      r12, r10                                      #49.30
        mov       QWORD PTR [72+rsp], rsi                       #324.33
        mov       QWORD PTR [80+rsp], rdi                       #324.33
        mov       QWORD PTR [144+rsp], r12                      #49.30[spill]
        mov       QWORD PTR [64+rsp], r12                       #324.33
        vmovups   XMMWORD PTR [rsp], xmm0                       #325.20
        vmovups   XMMWORD PTR [16+rsp], xmm0                    #325.20
        mov       rsi, QWORD PTR [280+rsp]                      #188.33[spill]
        mov       rdx, rsi                                      #188.33
        mov       rdi, QWORD PTR [304+rsp]                      #189.33[spill]
        xor       r9d, r9d                                      #192.32
        mov       r15, -1                                       #192.32
        xor       r12d, r12d                                    #192.32
        mulx      rbx, r8, rsi                                  #188.33
        mulx      rbp, r11, rdi                                 #189.33
        adox      r8, rbp                                       #192.32
        vpxor     xmm0, xmm0, xmm0                              #326.20
        mulx      rax, r10, QWORD PTR [296+rsp]                 #190.33[spill]
        adox      r11, rax                                      #193.32
        mulx      r13, r14, QWORD PTR [288+rsp]                 #191.33[spill]
        mov       rdx, rbx                                      #196.33
        adox      r10, r13                                      #194.32
        mov       r13, 0x0ffffffff                              #197.33
        mulx      rbp, rax, r15                                 #196.33
        seto      r12b                                          #194.32
        clc                                                     #195.30
        adcx      r12, r14                                      #195.30
        mov       r14, 0xffffffff00000001                       #198.33
        mulx      r14, r15, r14                                 #198.33
        mulx      r13, rcx, r13                                 #197.33
        mov       edx, r9d                                      #199.32
        adox      edx, r9d                                      #199.32
        mov       edx, r9d                                      #201.32
        adox      rax, r13                                      #199.32
        mov       r13d, 0                                       #200.32
        adox      rcx, r13                                      #200.32
        adox      r14, r13                                      #201.32
        seto      dl                                            #201.32
        clc                                                     #202.30
        adcx      rdx, r15                                      #202.30
        mov       r15d, r9d                                     #203.30
        adox      r15d, r9d                                     #203.30
        adox      rbx, rbp                                      #203.30
        mov       ebp, r9d                                      #207.32
        adox      r8, rax                                       #204.32
        adox      r11, rcx                                      #205.32
        adox      r10, r14                                      #206.32
        adox      r12, rdx                                      #207.32
        mov       rdx, rdi                                      #208.33
        mulx      rsi, r14, rsi                                 #208.33
        seto      bpl                                           #207.32
        clc                                                     #212.32
        mulx      rbx, rax, rdi                                 #209.33
        adcx      r14, rbx                                      #212.32
        mov       rbx, QWORD PTR [296+rsp]                      #210.33[spill]
        mulx      r15, rcx, rbx                                 #210.33
        adcx      rax, r15                                      #213.32
        mulx      rdi, r15, QWORD PTR [288+rsp]                 #211.33[spill]
        mov       edx, r9d                                      #215.30
        adcx      rcx, rdi                                      #214.32
        mov       edi, r9d                                      #214.32
        setb      dil                                           #214.32
        adox      edx, r9d                                      #215.30
        adox      rdi, r15                                      #215.30
        mov       r15d, r9d                                     #215.30
        seto      r15b                                          #215.30
        clc                                                     #216.34
        adcx      r8, rsi                                       #216.34
        mov       esi, r9d                                      #220.34
        mov       rdx, r8                                       #221.35
        adcx      r11, r14                                      #217.34
        mov       r14, 0xffffffff00000001                       #223.35
        adcx      r10, rax                                      #218.34
        mov       rax, -1                                       #221.35
        adcx      r12, rcx                                      #219.34
        adcx      rbp, rdi                                      #220.34
        mulx      r15, rdi, rax                                 #221.35
        mov       rax, 0x0ffffffff                              #222.35
        setb      sil                                           #220.34
        mov       DWORD PTR [64+rsp], esi                       #220.34[spill]
        mulx      rcx, rax, rax                                 #222.35
        mulx      r14, rsi, r14                                 #223.35
        mov       edx, r9d                                      #224.34
        adox      edx, r9d                                      #224.34
        mov       rdx, rbx                                      #234.35
        adox      rdi, rcx                                      #224.34
        mov       ecx, r9d                                      #226.34
        adox      rax, r13                                      #225.34
        adox      r14, r13                                      #226.34
        seto      cl                                            #226.34
        clc                                                     #227.31
        adcx      rcx, rsi                                      #227.31
        mov       esi, r9d                                      #228.31
        adox      esi, r9d                                      #228.31
        adox      r8, r15                                       #228.31
        mov       r15d, r9d                                     #232.34
        adox      r11, rdi                                      #229.34
        adox      r10, rax                                      #230.34
        mulx      r8, rax, QWORD PTR [280+rsp]                  #234.35[spill]
        adox      r12, r14                                      #231.34
        mulx      r14, rdi, QWORD PTR [304+rsp]                 #235.35[spill]
        adox      rbp, rcx                                      #232.34
        mulx      rcx, rsi, rbx                                 #236.35
        seto      r15b                                          #232.34
        clc                                                     #238.34
        adcx      rax, r14                                      #238.34
        adcx      rdi, rcx                                      #239.34
        mov       rcx, QWORD PTR [288+rsp]                      #237.35[spill]
        mulx      r14, rbx, rcx                                 #237.35
        mov       edx, r9d                                      #241.31
        adcx      rsi, r14                                      #240.34
        mov       r14d, r9d                                     #240.34
        setb      r14b                                          #240.34
        adox      edx, r9d                                      #241.31
        adox      r14, rbx                                      #241.31
        clc                                                     #242.34
        adcx      r11, r8                                       #242.34
        mov       r8d, r9d                                      #245.34
        mov       rdx, r11                                      #247.35
        adcx      r10, rax                                      #243.34
        mov       eax, DWORD PTR [64+rsp]                       #246.34[spill]
        adcx      r12, rdi                                      #244.34
        mov       rdi, 0x0ffffffff                              #248.35
        adcx      rbp, rsi                                      #245.34
        setb      r8b                                           #245.34
        xor       ebx, ebx                                      #245.34
        add       eax, r15d                                     #246.34
        cmp       r9d, r8d                                      #246.34
        mov       r15, 0xffffffff00000001                       #249.35
        mulx      r15, rsi, r15                                 #249.35
        adcx      rax, r14                                      #246.34
        mov       r14, -1                                       #247.35
        setb      bl                                            #246.34
        mov       DWORD PTR [72+rsp], ebx                       #246.34[spill]
        mulx      r8, rbx, r14                                  #247.35
        mulx      rdi, r14, rdi                                 #248.35
        mov       edx, r9d                                      #250.34
        adox      edx, r9d                                      #250.34
        mov       rdx, rcx                                      #260.35
        adox      rbx, rdi                                      #250.34
        mov       edi, r9d                                      #252.34
        adox      r14, r13                                      #251.34
        adox      r15, r13                                      #252.34
        seto      dil                                           #252.34
        clc                                                     #253.31
        adcx      rdi, rsi                                      #253.31
        mov       esi, r9d                                      #254.31
        adox      esi, r9d                                      #254.31
        adox      r11, r8                                       #254.31
        mulx      r11, rsi, QWORD PTR [304+rsp]                 #261.35[spill]
        adox      r10, rbx                                      #255.34
        adox      r12, r14                                      #256.34
        mov       r14d, r9d                                     #266.34
        adox      rbp, r15                                      #257.34
        mov       r15d, r9d                                     #258.34
        adox      rax, rdi                                      #258.34
        mulx      r8, rdi, QWORD PTR [280+rsp]                  #260.35[spill]
        seto      r15b                                          #258.34
        clc                                                     #264.34
        adcx      rdi, r11                                      #264.34
        mulx      rbx, r11, QWORD PTR [296+rsp]                 #262.35[spill]
        adcx      rsi, rbx                                      #265.34
        mulx      rcx, rbx, rcx                                 #263.35
        adcx      r11, rcx                                      #266.34
        mov       ecx, r9d                                      #267.31
        setb      r14b                                          #266.34
        adox      ecx, r9d                                      #267.31
        adox      r14, rbx                                      #267.31
        clc                                                     #268.34
        mov       ebx, DWORD PTR [72+rsp]                       #272.34[spill]
        adcx      r10, r8                                       #268.34
        mov       r8d, r9d                                      #271.34
        mov       rdx, r10                                      #273.35
        adcx      r12, rdi                                      #269.34
        mov       rdi, 0xffffffff00000001                       #275.35
        adcx      rbp, rsi                                      #270.34
        mulx      rdi, rsi, rdi                                 #275.35
        adcx      rax, r11                                      #271.34
        mov       r11, -1                                       #273.35
        mulx      rcx, r11, r11                                 #273.35
        setb      r8b                                           #271.34
        add       ebx, r15d                                     #272.34
        cmp       r9d, r8d                                      #272.34
        mov       r8, 0x0ffffffff                               #274.35
        mulx      r15, r8, r8                                   #274.35
        mov       edx, r9d                                      #276.34
        adcx      rbx, r14                                      #272.34
        mov       r14d, r9d                                     #272.34
        setb      r14b                                          #272.34
        adox      edx, r9d                                      #276.34
        adox      r11, r15                                      #276.34
        mov       r15d, r9d                                     #278.34
        adox      r8, r13                                       #277.34
        adox      rdi, r13                                      #278.34
        seto      r15b                                          #278.34
        clc                                                     #279.31
        adcx      r15, rsi                                      #279.31
        mov       esi, r9d                                      #280.31
        adox      esi, r9d                                      #280.31
        adox      r10, rcx                                      #280.31
        mov       rcx, 0x0ffffffff                              #287.34
        mov       r10d, r9d                                     #284.34
        adox      r12, r11                                      #281.34
        mov       rdx, r12                                      #286.34
        adox      rbp, r8                                       #282.34
        adox      rax, rdi                                      #283.34
        mov       rdi, 0xffffffff00000001                       #289.34
        adox      rbx, r15                                      #284.34
        mov       r15, rax                                      #288.34
        mov       r11, rbx                                      #289.34
        seto      r10b                                          #284.34
        xor       r8d, r8d                                      #284.34
        add       r14d, r10d                                    #290.31
        mov       r10, -1                                       #286.34
        sub       rdx, r10                                      #286.34
        mov       r10, rbp                                      #287.34
        sbb       r10, rcx                                      #287.34
        sbb       r15, r13                                      #288.34
        sbb       r11, rdi                                      #289.34
        setb      r8b                                           #289.34
        cmp       r9d, r8d                                      #290.31
        sbb       r14, r13                                      #290.31
        setb      r9b                                           #290.31
        dec       r9                                            #9.35
        and       r11, r9                                       #10.31
        and       r15, r9                                       #10.31
        and       r10, r9                                       #10.31
        and       rdx, r9                                       #10.31
        not       r9                                            #10.43
        and       rbx, r9                                       #10.60
        and       rax, r9                                       #10.60
        and       rbp, r9                                       #10.60
        and       r9, r12                                       #10.60
        or        r11, rbx                                      #10.60
        or        r15, rax                                      #10.60
        or        r10, rbp                                      #10.60
        or        rdx, r9                                       #10.60
        mov       QWORD PTR [376+rsp], r11                      #10.60[spill]
        mov       QWORD PTR [rsp], r11                          #325.37
        mov       QWORD PTR [400+rsp], r15                      #10.60[spill]
        mov       QWORD PTR [8+rsp], r15                        #325.37
        mov       QWORD PTR [392+rsp], r10                      #10.60[spill]
        mov       QWORD PTR [384+rsp], rdx                      #10.60[spill]
        mov       QWORD PTR [16+rsp], r10                       #325.37
        mov       QWORD PTR [24+rsp], rdx                       #325.37
        vmovups   XMMWORD PTR [32+rsp], xmm0                    #326.20
        vmovups   XMMWORD PTR [48+rsp], xmm0                    #326.20
        mov       r12, QWORD PTR [144+rsp]                      #188.33[spill]
        mov       rdx, r12                                      #188.33
        mov       r13, QWORD PTR [128+rsp]                      #189.33[spill]
        xor       r9d, r9d                                      #192.32
        xor       ebx, ebx                                      #192.32
        xor       r10d, r10d                                    #192.32
        mulx      r15, r14, r12                                 #188.33
        mulx      r11, rdi, r13                                 #189.33
        adcx      r14, r11                                      #192.32
        mov       r11, -1                                       #196.33
        vpxor     xmm0, xmm0, xmm0                              #327.21
        mulx      rbp, r8, QWORD PTR [136+rsp]                  #190.33[spill]
        adcx      rdi, rbp                                      #193.32
        mov       rbp, 0xffffffff00000001                       #198.33
        mulx      rsi, rcx, QWORD PTR [120+rsp]                 #191.33[spill]
        mov       rdx, r15                                      #196.33
        adcx      r8, rsi                                       #194.32
        mulx      rsi, rbp, rbp                                 #198.33
        setb      r10b                                          #194.32
        adox      ebx, r9d                                      #195.30
        adox      r10, rcx                                      #195.30
        mulx      rcx, rax, r11                                 #196.33
        mov       r11, 0x0ffffffff                              #197.33
        clc                                                     #199.32
        mulx      r11, rbx, r11                                 #197.33
        mov       edx, r9d                                      #202.30
        adcx      rax, r11                                      #199.32
        mov       r11d, 0                                       #200.32
        adcx      rbx, r11                                      #200.32
        adcx      rsi, r11                                      #201.32
        mov       r11d, r9d                                     #201.32
        setb      r11b                                          #201.32
        adox      edx, r9d                                      #202.30
        mov       rdx, r13                                      #208.33
        adox      r11, rbp                                      #202.30
        clc                                                     #203.30
        adcx      r15, rcx                                      #203.30
        mulx      rcx, r15, QWORD PTR [136+rsp]                 #210.33[spill]
        adcx      r14, rax                                      #204.32
        adcx      rdi, rbx                                      #205.32
        adcx      r8, rsi                                       #206.32
        mulx      rax, rsi, r12                                 #208.33
        adcx      r10, r11                                      #207.32
        mov       r11d, r9d                                     #207.32
        mulx      rbx, r12, r13                                 #209.33
        mov       r13d, r9d                                     #212.32
        setb      r11b                                          #207.32
        adox      r13d, r9d                                     #212.32
        mulx      rdx, rbp, QWORD PTR [120+rsp]                 #211.33[spill]
        mov       r13, 0x0ffffffff                              #222.35
        adox      rsi, rbx                                      #212.32
        mov       ebx, r9d                                      #214.32
        adox      r12, rcx                                      #213.32
        mov       ecx, r9d                                      #216.34
        adox      r15, rdx                                      #214.32
        seto      bl                                            #214.32
        clc                                                     #215.30
        adcx      rbx, rbp                                      #215.30
        adox      ecx, r9d                                      #216.34
        mov       ebp, r9d                                      #220.34
        adox      r14, rax                                      #216.34
        mov       rdx, r14                                      #221.35
        adox      rdi, rsi                                      #217.34
        mov       rsi, -1                                       #221.35
        mulx      rcx, rax, rsi                                 #221.35
        adox      r8, r12                                       #218.34
        adox      r10, r15                                      #219.34
        mov       r15, 0xffffffff00000001                       #223.35
        mulx      rsi, r15, r15                                 #223.35
        adox      r11, rbx                                      #220.34
        mulx      r12, rbx, r13                                 #222.35
        mov       r13d, 0                                       #225.34
        seto      bpl                                           #220.34
        clc                                                     #224.34
        mov       rdx, QWORD PTR [136+rsp]                      #234.35[spill]
        adcx      rax, r12                                      #224.34
        mov       r12d, r9d                                     #227.31
        adcx      rbx, r13                                      #225.34
        adcx      rsi, r13                                      #226.34
        mov       r13d, r9d                                     #226.34
        setb      r13b                                          #226.34
        adox      r12d, r9d                                     #227.31
        adox      r13, r15                                      #227.31
        mov       r15d, r9d                                     #238.34
        clc                                                     #228.31
        adcx      r14, rcx                                      #228.31
        mov       r14d, r9d                                     #232.34
        adcx      rdi, rax                                      #229.34
        mulx      rcx, r12, rdx                                 #236.35
        adcx      r8, rbx                                       #230.34
        adcx      r10, rsi                                      #231.34
        adcx      r11, r13                                      #232.34
        mulx      rax, r13, QWORD PTR [144+rsp]                 #234.35[spill]
        setb      r14b                                          #232.34
        adox      r15d, r9d                                     #238.34
        mov       DWORD PTR [216+rsp], r14d                     #232.34[spill]
        mulx      rsi, r14, QWORD PTR [128+rsp]                 #235.35[spill]
        adox      r13, rsi                                      #238.34
        mov       esi, r9d                                      #240.34
        mulx      rdx, rbx, QWORD PTR [120+rsp]                 #237.35[spill]
        adox      r14, rcx                                      #239.34
        mov       ecx, r9d                                      #242.34
        adox      r12, rdx                                      #240.34
        seto      sil                                           #240.34
        clc                                                     #241.31
        adcx      rsi, rbx                                      #241.31
        adox      ecx, r9d                                      #242.34
        adox      rdi, rax                                      #242.34
        mov       eax, r9d                                      #245.34
        mov       rdx, rdi                                      #247.35
        adox      r8, r13                                       #243.34
        mov       r13, 0x0ffffffff                              #248.35
        adox      r10, r14                                      #244.34
        mov       r14, 0xffffffff00000001                       #249.35
        adox      r11, r12                                      #245.34
        mulx      r14, r12, r14                                 #249.35
        seto      al                                            #245.34
        xor       ebx, ebx                                      #245.34
        add       ebp, DWORD PTR [216+rsp]                      #246.34[spill]
        cmp       r9d, eax                                      #246.34
        mulx      r13, rax, r13                                 #248.35
        adcx      rbp, rsi                                      #246.34
        mov       rsi, -1                                       #247.35
        mulx      rcx, r15, rsi                                 #247.35
        mov       edx, r9d                                      #250.34
        setb      bl                                            #246.34
        adox      edx, r9d                                      #250.34
        mov       rdx, QWORD PTR [120+rsp]                      #260.35[spill]
        adox      r15, r13                                      #250.34
        mov       r13d, 0                                       #251.34
        adox      rax, r13                                      #251.34
        adox      r14, r13                                      #252.34
        mov       r13d, r9d                                     #252.34
        seto      r13b                                          #252.34
        clc                                                     #253.31
        adcx      r13, r12                                      #253.31
        mov       r12d, r9d                                     #254.31
        adox      r12d, r9d                                     #254.31
        adox      rdi, rcx                                      #254.31
        mov       ecx, r9d                                      #258.34
        mulx      rdi, r12, QWORD PTR [128+rsp]                 #261.35[spill]
        adox      r8, r15                                       #255.34
        adox      r10, rax                                      #256.34
        adox      r11, r14                                      #257.34
        adox      rbp, r13                                      #258.34
        mulx      r13, r15, QWORD PTR [144+rsp]                 #260.35[spill]
        seto      cl                                            #258.34
        clc                                                     #264.34
        adcx      r15, rdi                                      #264.34
        mulx      rdi, r14, QWORD PTR [136+rsp]                 #262.35[spill]
        adcx      r12, rdi                                      #265.34
        mulx      rdi, rax, rdx                                 #263.35
        mov       edx, r9d                                      #267.31
        adcx      r14, rdi                                      #266.34
        mov       edi, r9d                                      #266.34
        setb      dil                                           #266.34
        adox      edx, r9d                                      #267.31
        adox      rdi, rax                                      #267.31
        clc                                                     #268.34
        adcx      r8, r13                                       #268.34
        mov       r13d, r9d                                     #271.34
        mov       rdx, r8                                       #273.35
        adcx      r10, r15                                      #269.34
        mov       r15, 0xffffffff00000001                       #275.35
        adcx      r11, r12                                      #270.34
        adcx      rbp, r14                                      #271.34
        setb      r13b                                          #271.34
        xor       eax, eax                                      #271.34
        add       ebx, ecx                                      #272.34
        cmp       r9d, r13d                                     #272.34
        mov       rcx, 0x0ffffffff                              #274.35
        mulx      r14, r13, rsi                                 #273.35
        adcx      rbx, rdi                                      #272.34
        mulx      rcx, r12, rcx                                 #274.35
        mulx      rdi, r15, r15                                 #275.35
        mov       edx, r9d                                      #276.34
        setb      al                                            #272.34
        adox      edx, r9d                                      #276.34
        mov       edx, r9d                                      #278.34
        adox      r13, rcx                                      #276.34
        mov       ecx, 0                                        #277.34
        adox      r12, rcx                                      #277.34
        adox      rdi, rcx                                      #278.34
        seto      dl                                            #278.34
        clc                                                     #279.31
        adcx      rdx, r15                                      #279.31
        mov       r15d, r9d                                     #280.31
        adox      r15d, r9d                                     #280.31
        adox      r8, r14                                       #280.31
        mov       r8d, r9d                                      #284.34
        adox      r10, r13                                      #281.34
        adox      r11, r12                                      #282.34
        adox      rbp, rdi                                      #283.34
        mov       rdi, r10                                      #286.34
        adox      rbx, rdx                                      #284.34
        mov       rdx, 0x0ffffffff                              #287.34
        mov       r13, rbx                                      #289.34
        seto      r8b                                           #284.34
        xor       r12d, r12d                                    #284.34
        add       eax, r8d                                      #290.31
        sub       rdi, rsi                                      #286.34
        mov       rsi, r11                                      #287.34
        mov       r8, 0xffffffff00000001                        #289.34
        sbb       rsi, rdx                                      #287.34
        mov       rdx, rbp                                      #288.34
        sbb       rdx, rcx                                      #288.34
        sbb       r13, r8                                       #289.34
        setb      r12b                                          #289.34
        cmp       r9d, r12d                                     #290.31
        sbb       rax, rcx                                      #290.31
        setb      r9b                                           #290.31
        dec       r9                                            #9.35
        and       r13, r9                                       #10.31
        and       rdx, r9                                       #10.31
        and       rsi, r9                                       #10.31
        and       rdi, r9                                       #10.31
        not       r9                                            #10.43
        and       rbx, r9                                       #10.60
        and       rbp, r9                                       #10.60
        and       r11, r9                                       #10.60
        and       r9, r10                                       #10.60
        or        r13, rbx                                      #10.60
        or        rdx, rbp                                      #10.60
        or        rsi, r11                                      #10.60
        or        rdi, r9                                       #10.60
        mov       QWORD PTR [312+rsp], r13                      #10.60[spill]
        mov       QWORD PTR [32+rsp], r13                       #326.37
        mov       QWORD PTR [40+rsp], rdx                       #326.37
        mov       QWORD PTR [48+rsp], rsi                       #326.37
        mov       QWORD PTR [56+rsp], rdi                       #326.37
        vmovups   XMMWORD PTR [64+rsp], xmm0                    #327.21
        vmovups   XMMWORD PTR [80+rsp], xmm0                    #327.21
        mov       r8, QWORD PTR [192+rsp]                       #14.23[spill]
        mov       rax, QWORD PTR [256+rsp]                      #14.23[spill]
        vpxor     xmm0, xmm0, xmm0                              #336.21
        mov       QWORD PTR [352+rsp], rdi                      #[spill]
        mov       rdi, QWORD PTR [168+rsp]                      #14.23[spill]
        or        r8, QWORD PTR [184+rsp]                       #14.23[spill]
        or        rax, QWORD PTR [248+rsp]                      #14.23[spill]
        mov       QWORD PTR [360+rsp], rsi                      #[spill]
        mov       rsi, QWORD PTR [200+rsp]                      #15.23[spill]
        mov       r15, QWORD PTR [264+rsp]                      #15.23[spill]
        or        rsi, r8                                       #15.23
        or        rdi, QWORD PTR [160+rsp]                      #14.23[spill]
        or        r15, rax                                      #15.23
        or        QWORD PTR [176+rsp], rdi                      #15.23[spill]
        or        QWORD PTR [208+rsp], rsi                      #16.23[spill]
        or        QWORD PTR [272+rsp], r15                      #16.23[spill]
        xor       r8d, r8d                                      #77.32
        xor       esi, esi                                      #77.32
        xor       r15d, r15d                                    #77.32
        xor       r13d, r13d                                    #77.32
        mov       QWORD PTR [368+rsp], rdx                      #[spill]
        mov       r13, 0x0ffffffff                              #82.33
        mov       rdx, QWORD PTR [376+rsp]                      #73.33[spill]
        mov       r9, QWORD PTR [280+rsp]                       #73.33[spill]
        mov       r10, QWORD PTR [304+rsp]                      #74.33[spill]
        mulx      r12, r11, r9                                  #73.33
        mulx      rcx, rbx, r10                                 #74.33
        adcx      r11, rcx                                      #77.32
        mulx      rdi, rbp, QWORD PTR [296+rsp]                 #75.33[spill]
        adcx      rbx, rdi                                      #78.32
        mov       edi, 0                                        #79.32
        mulx      r14, rax, QWORD PTR [288+rsp]                 #76.33[spill]
        adcx      rbp, r14                                      #79.32
        mov       rdx, r12                                      #81.33
        setb      r8b                                           #79.32
        adox      esi, edi                                      #80.30
        mov       rsi, -1                                       #81.33
        adox      r8, rax                                       #80.30
        mov       rax, 0xffffffff00000001                       #83.33
        mulx      rcx, r14, rsi                                 #81.33
        seto      r15b                                          #80.30
        clc                                                     #84.32
        mulx      rsi, r13, r13                                 #82.33
        adcx      r14, rsi                                      #84.32
        mov       esi, 0                                        #85.32
        mulx      r15, rax, rax                                 #83.33
        mov       edx, edi                                      #87.30
        adcx      r13, rsi                                      #85.32
        adcx      r15, rsi                                      #86.32
        mov       esi, edi                                      #86.32
        setb      sil                                           #86.32
        adox      edx, edi                                      #87.30
        adox      rsi, rax                                      #87.30
        mov       rdx, QWORD PTR [400+rsp]                      #93.33[spill]
        clc                                                     #88.30
        adcx      r12, rcx                                      #88.30
        adcx      r11, r14                                      #89.32
        mulx      r14, r12, r9                                  #93.33
        adcx      rbx, r13                                      #90.32
        mulx      r13, r9, QWORD PTR [296+rsp]                  #95.33[spill]
        adcx      rbp, r15                                      #91.32
        mulx      r15, rcx, r10                                 #94.33
        mov       r10d, edi                                     #97.32
        adcx      r8, rsi                                       #92.32
        mov       esi, edi                                      #92.32
        mulx      rdx, rax, QWORD PTR [288+rsp]                 #96.33[spill]
        setb      sil                                           #92.32
        adox      r10d, edi                                     #97.32
        mov       r10, 0x0ffffffff                              #107.35
        adox      r12, r15                                      #97.32
        mov       r15d, edi                                     #99.32
        adox      rcx, r13                                      #98.32
        mov       r13d, edi                                     #101.34
        adox      r9, rdx                                       #99.32
        seto      r15b                                          #99.32
        clc                                                     #100.30
        adcx      r15, rax                                      #100.30
        adox      r13d, edi                                     #101.34
        mov       eax, edi                                      #105.34
        adox      r11, r14                                      #101.34
        mov       r14, 0xffffffff00000001                       #108.35
        mov       rdx, r11                                      #106.35
        adox      rbx, r12                                      #102.34
        adox      rbp, rcx                                      #103.34
        mov       rcx, -1                                       #106.35
        adox      r8, r9                                        #104.34
        mulx      r13, r9, rcx                                  #106.35
        adox      rsi, r15                                      #105.34
        mulx      r12, r15, r10                                 #107.35
        mov       r10d, 0                                       #110.34
        seto      al                                            #105.34
        clc                                                     #109.34
        adcx      r9, r12                                       #109.34
        mulx      r12, rcx, r14                                 #108.35
        mov       r14d, edi                                     #112.31
        adcx      r15, r10                                      #110.34
        mov       rdx, QWORD PTR [392+rsp]                      #119.35[spill]
        adcx      r12, r10                                      #111.34
        mov       r10d, edi                                     #111.34
        setb      r10b                                          #111.34
        adox      r14d, edi                                     #112.31
        adox      r10, rcx                                      #112.31
        clc                                                     #113.31
        adcx      r11, r13                                      #113.31
        mulx      r13, r11, QWORD PTR [296+rsp]                 #121.35[spill]
        adcx      rbx, r9                                       #114.34
        mov       r9d, edi                                      #117.34
        adcx      rbp, r15                                      #115.34
        mulx      r15, r14, QWORD PTR [304+rsp]                 #120.35[spill]
        adcx      r8, r12                                       #116.34
        mov       r12d, edi                                     #123.34
        adcx      rsi, r10                                      #117.34
        setb      r9b                                           #117.34
        adox      r12d, edi                                     #123.34
        mov       DWORD PTR [408+rsp], r9d                      #117.34[spill]
        mulx      r9, r10, QWORD PTR [280+rsp]                  #119.35[spill]
        adox      r10, r15                                      #123.34
        mov       r15d, edi                                     #125.34
        mulx      rdx, rcx, QWORD PTR [288+rsp]                 #122.35[spill]
        adox      r14, r13                                      #124.34
        mov       r13d, edi                                     #126.31
        adox      r11, rdx                                      #125.34
        seto      r15b                                          #125.34
        clc                                                     #126.31
        adcx      r15, rcx                                      #126.31
        mov       ecx, edi                                      #127.34
        setb      r13b                                          #126.31
        adox      ecx, edi                                      #127.34
        mov       rcx, -1                                       #132.35
        adox      rbx, r9                                       #127.34
        mov       r9, 0x0ffffffff                               #133.35
        mov       rdx, rbx                                      #132.35
        adox      rbp, r10                                      #128.34
        mulx      r13, r12, rcx                                 #132.35
        adox      r8, r14                                       #129.34
        mulx      r10, r14, r9                                  #133.35
        adox      rsi, r11                                      #130.34
        mov       r11d, edi                                     #130.34
        seto      r11b                                          #130.34
        add       eax, DWORD PTR [408+rsp]                      #131.34[spill]
        cmp       edi, r11d                                     #131.34
        mov       r11, 0xffffffff00000001                       #134.35
        adcx      rax, r15                                      #131.34
        mov       r15d, edi                                     #131.34
        mulx      r9, r11, r11                                  #134.35
        mov       edx, edi                                      #135.34
        setb      r15b                                          #131.34
        adox      edx, edi                                      #135.34
        mov       rdx, QWORD PTR [384+rsp]                      #145.35[spill]
        adox      r12, r10                                      #135.34
        mov       r10d, 0                                       #136.34
        adox      r14, r10                                      #136.34
        adox      r9, r10                                       #137.34
        mov       r10d, edi                                     #137.34
        seto      r10b                                          #137.34
        clc                                                     #138.31
        adcx      r10, r11                                      #138.31
        mov       r11d, edi                                     #139.31
        adox      r11d, edi                                     #139.31
        adox      rbx, r13                                      #139.31
        mov       r13d, edi                                     #143.34
        adox      rbp, r12                                      #140.34
        mulx      rbx, r12, QWORD PTR [280+rsp]                 #145.35[spill]
        adox      r8, r14                                       #141.34
        adox      rsi, r9                                       #142.34
        mulx      r14, r9, QWORD PTR [304+rsp]                  #146.35[spill]
        adox      rax, r10                                      #143.34
        mulx      r10, r11, QWORD PTR [296+rsp]                 #147.35[spill]
        seto      r13b                                          #143.34
        clc                                                     #149.34
        adcx      r12, r14                                      #149.34
        adcx      r9, r10                                       #150.34
        mulx      r10, r14, QWORD PTR [288+rsp]                 #148.35[spill]
        mov       edx, edi                                      #152.31
        adcx      r11, r10                                      #151.34
        mov       r10d, edi                                     #151.34
        setb      r10b                                          #151.34
        adox      edx, edi                                      #152.31
        adox      r10, r14                                      #152.31
        clc                                                     #153.34
        adcx      rbp, rbx                                      #153.34
        mov       ebx, edi                                      #156.34
        mov       rdx, rbp                                      #158.35
        adcx      r8, r12                                       #154.34
        adcx      rsi, r9                                       #155.34
        mov       r9, 0x0ffffffff                               #159.35
        adcx      rax, r11                                      #156.34
        mulx      r9, r11, r9                                   #159.35
        setb      bl                                            #156.34
        add       r15d, r13d                                    #157.34
        cmp       edi, ebx                                      #157.34
        mov       rbx, 0xffffffff00000001                       #160.35
        mulx      r13, r14, rcx                                 #158.35
        adcx      r15, r10                                      #157.34
        mov       r10d, edi                                     #157.34
        mulx      rbx, r12, rbx                                 #160.35
        mov       edx, edi                                      #161.34
        setb      r10b                                          #157.34
        adox      edx, edi                                      #161.34
        mov       edx, edi                                      #163.34
        adox      r14, r9                                       #161.34
        mov       r9d, 0                                        #162.34
        adox      r11, r9                                       #162.34
        adox      rbx, r9                                       #163.34
        seto      dl                                            #163.34
        clc                                                     #164.31
        adcx      rdx, r12                                      #164.31
        mov       r12d, edi                                     #165.31
        adox      r12d, edi                                     #165.31
        adox      rbp, r13                                      #165.31
        mov       ebp, edi                                      #169.34
        adox      r8, r14                                       #166.34
        mov       r13, r8                                       #171.34
        adox      rsi, r11                                      #167.34
        mov       r11, 0xffffffff00000001                       #174.34
        adox      rax, rbx                                      #168.34
        mov       rbx, QWORD PTR [152+rsp]                      #16.23[spill]
        adox      r15, rdx                                      #169.34
        mov       rdx, rsi                                      #172.34
        seto      bpl                                           #169.34
        xor       r12d, r12d                                    #169.34
        xor       r14d, r14d                                    #169.34
        add       r10d, ebp                                     #175.31
        sub       r13, rcx                                      #171.34
        mov       rcx, 0x0ffffffff                              #172.34
        mov       rbp, r15                                      #174.34
        sbb       rdx, rcx                                      #172.34
        mov       rcx, rax                                      #173.34
        sbb       rcx, r9                                       #173.34
        sbb       rbp, r11                                      #174.34
        mov       r11, QWORD PTR [208+rsp]                      #322.29[spill]
        setb      r14b                                          #174.34
        cmp       edi, r14d                                     #175.31
        sbb       r10, r9                                       #175.31
        mov       r9d, edi                                      #175.31
        setb      r9b                                           #175.31
        mov       r10d, 1                                       #175.31
        or        rbx, QWORD PTR [176+rsp]                      #16.23[spill]
        cmove     r12d, r10d                                    #328.5
        dec       r9                                            #9.35
        and       rbp, r9                                       #10.31
        and       rcx, r9                                       #10.31
        and       rdx, r9                                       #10.31
        and       r13, r9                                       #10.31
        not       r9                                            #10.43
        and       rsi, r9                                       #10.60
        dec       r12                                           #9.35
        or        rdx, rsi                                      #10.60
        mov       rsi, r12                                      #10.43
        and       r15, r9                                       #10.60
        and       rax, r9                                       #10.60
        and       r9, r8                                        #10.60
        not       rsi                                           #10.43
        mov       r8, QWORD PTR [104+rsp]                       #328.25[spill]
        or        rcx, rax                                      #10.60
        mov       rax, rsi                                      #10.60
        or        rbp, r15                                      #10.60
        or        r11, QWORD PTR [272+rsp]                      #322.29[spill]
        mov       r15, QWORD PTR [88+r8]                        #328.25
        mov       QWORD PTR [336+rsp], rdx                      #10.60[spill]
        cmove     edi, r10d                                     #332.5
        and       r15, r12                                      #10.31
        and       rax, 1                                        #10.60
        mov       QWORD PTR [80+rsp], rdx                       #327.35
        mov       rdx, 0xffffffff00000000                       #10.60
        or        r15, rax                                      #10.60
        and       rdx, rsi                                      #10.60
        mov       rax, QWORD PTR [80+r8]                        #329.25
        or        r13, r9                                       #10.60
        and       rax, r12                                      #10.31
        mov       QWORD PTR [344+rsp], rcx                      #10.60[spill]
        or        rax, rdx                                      #10.60
        mov       QWORD PTR [72+rsp], rcx                       #327.35
        mov       rdx, QWORD PTR [72+r8]                        #330.25
        mov       rcx, QWORD PTR [64+r8]                        #331.25
        and       rdx, r12                                      #10.31
        mov       QWORD PTR [320+rsp], rbp                      #10.60[spill]
        and       rcx, r12                                      #10.31
        mov       QWORD PTR [64+rsp], rbp                       #327.35
        or        rdx, rsi                                      #10.60
        or        rcx, rsi                                      #10.60
        mov       rbp, QWORD PTR [112+rsp]                      #332.32[spill]
        dec       rdi                                           #9.35
        mov       QWORD PTR [88+r8], r15                        #328.5
        and       r15, rdi                                      #10.31
        mov       QWORD PTR [80+r8], rax                        #329.5
        and       rax, rdi                                      #10.31
        mov       QWORD PTR [72+r8], rdx                        #330.5
        and       rdx, rdi                                      #10.31
        mov       QWORD PTR [64+r8], rcx                        #331.5
        and       rcx, rdi                                      #10.31
        mov       QWORD PTR [232+rsp], rdi                      #9.35[spill]
        not       rdi                                           #10.43
        mov       QWORD PTR [328+rsp], r13                      #10.60[spill]
        mov       QWORD PTR [88+rsp], r13                       #327.35
        mov       r13, QWORD PTR [88+rbp]                       #332.32
        and       r13, rdi                                      #10.60
        or        r15, r13                                      #10.60
        mov       QWORD PTR [88+r8], r15                        #332.5
        mov       r13, QWORD PTR [80+rbp]                       #333.32
        and       r13, rdi                                      #10.60
        or        rax, r13                                      #10.60
        mov       QWORD PTR [80+r8], rax                        #333.5
        mov       QWORD PTR [224+rsp], rsi                      #10.43[spill]
        mov       rsi, QWORD PTR [72+rbp]                       #334.32
        and       rsi, rdi                                      #10.60
        or        rdx, rsi                                      #10.60
        mov       QWORD PTR [72+r8], rdx                        #334.5
        mov       QWORD PTR [240+rsp], r12                      #9.35[spill]
        mov       r12, QWORD PTR [64+rbp]                       #335.32
        and       r12, rdi                                      #10.60
        or        rcx, r12                                      #10.60
        mov       QWORD PTR [216+rsp], rdi                      #10.43[spill]
        mov       QWORD PTR [64+r8], rcx                        #335.5
        vmovups   XMMWORD PTR [32+rsp], xmm0                    #336.21
        vmovups   XMMWORD PTR [48+rsp], xmm0                    #336.21
        mov       rdx, QWORD PTR [368+rsp]                      #336.21[spill]
        mov       rsi, QWORD PTR [360+rsp]                      #336.21[spill]
        mov       rdi, QWORD PTR [352+rsp]                      #336.21[spill]
        mov       r9, rbp                                       #73.33
        xor       ebp, ebp                                      #77.32
        mov       QWORD PTR [368+rsp], rdx                      #[spill]
        xor       r11d, r11d                                    #80.30
        mov       QWORD PTR [352+rsp], rdi                      #[spill]
        mov       rdx, QWORD PTR [376+rsp]                      #73.33[spill]
        xor       edi, edi                                      #77.32
        mulx      r12, r10, QWORD PTR [r9]                      #73.33
        mulx      r8, r14, QWORD PTR [8+r9]                     #74.33
        vpxor     xmm0, xmm0, xmm0                              #337.21
        adcx      r10, r8                                       #77.32
        mov       QWORD PTR [360+rsp], rsi                      #[spill]
        mulx      rcx, rsi, QWORD PTR [16+r9]                   #75.33
        adcx      r14, rcx                                      #78.32
        mov       rcx, -1                                       #81.33
        mulx      rax, r15, QWORD PTR [24+r9]                   #76.33
        mov       rdx, r12                                      #81.33
        adcx      rsi, rax                                      #79.32
        mov       rax, 0x0ffffffff                              #82.33
        mulx      r13, rbx, rcx                                 #81.33
        setb      dil                                           #79.32
        adox      r11d, ebp                                     #80.30
        adox      rdi, r15                                      #80.30
        mov       r15, 0xffffffff00000001                       #83.33
        mulx      r11, rax, rax                                 #82.33
        clc                                                     #84.32
        mulx      rcx, r8, r15                                  #83.33
        mov       r15d, ebp                                     #87.30
        adcx      rbx, r11                                      #84.32
        mov       r11d, 0                                       #85.32
        mov       rdx, QWORD PTR [400+rsp]                      #93.33[spill]
        adcx      rax, r11                                      #85.32
        adcx      rcx, r11                                      #86.32
        mov       r11d, ebp                                     #86.32
        setb      r11b                                          #86.32
        adox      r15d, ebp                                     #87.30
        adox      r11, r8                                       #87.30
        clc                                                     #88.30
        mov       r8d, ebp                                      #92.32
        adcx      r12, r13                                      #88.30
        mulx      r13, r12, QWORD PTR [8+r9]                    #94.33
        adcx      r10, rbx                                      #89.32
        adcx      r14, rax                                      #90.32
        mulx      rax, rbx, QWORD PTR [r9]                      #93.33
        adcx      rsi, rcx                                      #91.32
        adcx      rdi, r11                                      #92.32
        mulx      r11, r15, QWORD PTR [16+r9]                   #95.33
        mulx      rdx, rcx, QWORD PTR [24+r9]                   #96.33
        mov       r9d, ebp                                      #97.32
        setb      r8b                                           #92.32
        adox      r9d, ebp                                      #97.32
        mov       r9, 0xffffffff00000001                        #108.35
        adox      rbx, r13                                      #97.32
        mov       r13d, ebp                                     #99.32
        adox      r12, r11                                      #98.32
        mov       r11d, ebp                                     #101.34
        adox      r15, rdx                                      #99.32
        seto      r13b                                          #99.32
        clc                                                     #100.30
        adcx      r13, rcx                                      #100.30
        adox      r11d, ebp                                     #101.34
        mov       ecx, ebp                                      #105.34
        adox      r10, rax                                      #101.34
        mov       rax, -1                                       #106.35
        mov       rdx, r10                                      #106.35
        adox      r14, rbx                                      #102.34
        mov       rbx, 0x0ffffffff                              #107.35
        adox      rsi, r12                                      #103.34
        adox      rdi, r15                                      #104.34
        mov       r15d, 0                                       #110.34
        adox      r8, r13                                       #105.34
        mulx      r11, r13, rax                                 #106.35
        seto      cl                                            #105.34
        clc                                                     #109.34
        mulx      rax, r12, rbx                                 #107.35
        adcx      r13, rax                                      #109.34
        mulx      rbx, rax, r9                                  #108.35
        mov       r9d, ebp                                      #111.34
        adcx      r12, r15                                      #110.34
        mov       rdx, QWORD PTR [392+rsp]                      #119.35[spill]
        adcx      rbx, r15                                      #111.34
        mov       r15d, ebp                                     #112.31
        setb      r9b                                           #111.34
        adox      r15d, ebp                                     #112.31
        adox      r9, rax                                       #112.31
        clc                                                     #113.31
        mov       eax, ebp                                      #123.34
        adcx      r10, r11                                      #113.31
        adcx      r14, r13                                      #114.34
        adcx      rsi, r12                                      #115.34
        mov       r12d, ebp                                     #117.34
        adcx      rdi, rbx                                      #116.34
        mov       rbx, QWORD PTR [112+rsp]                      #119.35[spill]
        adcx      r8, r9                                        #117.34
        mulx      r13, r9, QWORD PTR [rbx]                      #119.35
        setb      r12b                                          #117.34
        adox      eax, ebp                                      #123.34
        mov       DWORD PTR [152+rsp], r12d                     #117.34[spill]
        mov       eax, ebp                                      #125.34
        mulx      r12, r10, QWORD PTR [8+rbx]                   #120.35
        adox      r9, r12                                       #123.34
        mulx      r11, r15, QWORD PTR [16+rbx]                  #121.35
        adox      r10, r11                                      #124.34
        mulx      rdx, rbx, QWORD PTR [24+rbx]                  #122.35
        adox      r15, rdx                                      #125.34
        seto      al                                            #125.34
        clc                                                     #126.31
        adcx      rax, rbx                                      #126.31
        mov       ebx, ebp                                      #127.34
        adox      ebx, ebp                                      #127.34
        mov       rbx, -1                                       #132.35
        adox      r14, r13                                      #127.34
        mov       r13, 0x0ffffffff                              #133.35
        mov       rdx, r14                                      #132.35
        adox      rsi, r9                                       #128.34
        mov       r9, 0xffffffff00000001                        #134.35
        mulx      r12, r11, rbx                                 #132.35
        adox      rdi, r10                                      #129.34
        mov       r10d, ebp                                     #130.34
        adox      r8, r15                                       #130.34
        mulx      r15, r13, r13                                 #133.35
        seto      r10b                                          #130.34
        add       ecx, DWORD PTR [152+rsp]                      #131.34[spill]
        cmp       ebp, r10d                                     #131.34
        mulx      r9, r10, r9                                   #134.35
        mov       edx, ebp                                      #135.34
        adcx      rcx, rax                                      #131.34
        mov       eax, ebp                                      #131.34
        setb      al                                            #131.34
        adox      edx, ebp                                      #135.34
        mov       rdx, QWORD PTR [384+rsp]                      #145.35[spill]
        adox      r11, r15                                      #135.34
        mov       r15d, 0                                       #136.34
        adox      r13, r15                                      #136.34
        adox      r9, r15                                       #137.34
        mov       r15d, ebp                                     #137.34
        seto      r15b                                          #137.34
        clc                                                     #138.31
        adcx      r15, r10                                      #138.31
        mov       r10d, ebp                                     #139.31
        adox      r10d, ebp                                     #139.31
        adox      r14, r12                                      #139.31
        adox      rsi, r11                                      #140.34
        adox      rdi, r13                                      #141.34
        adox      r8, r9                                        #142.34
        mov       r9, QWORD PTR [112+rsp]                       #145.35[spill]
        adox      rcx, r15                                      #143.34
        mov       r15d, ebp                                     #143.34
        mulx      r14, r11, QWORD PTR [r9]                      #145.35
        seto      r15b                                          #143.34
        clc                                                     #149.34
        mulx      r12, r13, QWORD PTR [8+r9]                    #146.35
        adcx      r11, r12                                      #149.34
        mulx      r10, r12, QWORD PTR [16+r9]                   #147.35
        adcx      r13, r10                                      #150.34
        mulx      r9, r10, QWORD PTR [24+r9]                    #148.35
        mov       edx, ebp                                      #152.31
        adcx      r12, r9                                       #151.34
        mov       r9d, ebp                                      #151.34
        setb      r9b                                           #151.34
        adox      edx, ebp                                      #152.31
        adox      r9, r10                                       #152.31
        mov       r10d, ebp                                     #152.31
        seto      r10b                                          #152.31
        clc                                                     #153.34
        adcx      rsi, r14                                      #153.34
        mov       r14d, ebp                                     #156.34
        mov       rdx, rsi                                      #158.35
        adcx      rdi, r11                                      #154.34
        mov       r11, 0x0ffffffff                              #159.35
        adcx      r8, r13                                       #155.34
        mulx      r13, r11, r11                                 #159.35
        adcx      rcx, r12                                      #156.34
        setb      r14b                                          #156.34
        xor       r12d, r12d                                    #156.34
        add       eax, r15d                                     #157.34
        cmp       ebp, r14d                                     #157.34
        mov       r15, 0xffffffff00000001                       #160.35
        mulx      r10, r15, r15                                 #160.35
        adcx      rax, r9                                       #157.34
        mulx      r9, r14, rbx                                  #158.35
        mov       edx, ebp                                      #161.34
        setb      r12b                                          #157.34
        adox      edx, ebp                                      #161.34
        mov       edx, ebp                                      #163.34
        adox      r14, r13                                      #161.34
        mov       r13d, 0                                       #162.34
        adox      r11, r13                                      #162.34
        adox      r10, r13                                      #163.34
        seto      dl                                            #163.34
        clc                                                     #164.31
        adcx      rdx, r15                                      #164.31
        mov       r15d, ebp                                     #165.31
        adox      r15d, ebp                                     #165.31
        adox      rsi, r9                                       #165.31
        mov       r9, 0x0ffffffff                               #172.34
        mov       esi, ebp                                      #169.34
        adox      rdi, r14                                      #166.34
        adox      r8, r11                                       #167.34
        adox      rcx, r10                                      #168.34
        mov       r10, 0xffffffff00000001                       #174.34
        adox      rax, rdx                                      #169.34
        mov       rdx, rax                                      #174.34
        seto      sil                                           #169.34
        add       r12d, esi                                     #175.31
        mov       rsi, rdi                                      #171.34
        sub       rsi, rbx                                      #171.34
        mov       rbx, r8                                       #172.34
        sbb       rbx, r9                                       #172.34
        mov       r9, rcx                                       #173.34
        sbb       r9, r13                                       #173.34
        sbb       rdx, r10                                      #174.34
        mov       r10d, ebp                                     #174.34
        setb      r10b                                          #174.34
        cmp       ebp, r10d                                     #175.31
        sbb       r12, r13                                      #175.31
        setb      bpl                                           #175.31
        dec       rbp                                           #9.35
        and       rdx, rbp                                      #10.31
        and       r9, rbp                                       #10.31
        and       rbx, rbp                                      #10.31
        and       rsi, rbp                                      #10.31
        not       rbp                                           #10.43
        and       rax, rbp                                      #10.60
        and       rcx, rbp                                      #10.60
        and       r8, rbp                                       #10.60
        and       rbp, rdi                                      #10.60
        or        rdx, rax                                      #10.60
        or        r9, rcx                                       #10.60
        or        rbx, r8                                       #10.60
        or        rsi, rbp                                      #10.60
        mov       QWORD PTR [rsp], rdx                          #336.35
        mov       QWORD PTR [8+rsp], r9                         #336.35
        mov       QWORD PTR [16+rsp], rbx                       #336.35
        mov       QWORD PTR [24+rsp], rsi                       #336.35
        vmovups   XMMWORD PTR [64+rsp], xmm0                    #337.21
        vmovups   XMMWORD PTR [80+rsp], xmm0                    #337.21
        mov       rdx, QWORD PTR [368+rsp]                      #337.21[spill]
        mov       rsi, QWORD PTR [360+rsp]                      #337.21[spill]
        mov       rdi, QWORD PTR [352+rsp]                      #337.21[spill]
        mov       r12, QWORD PTR [32+rsp]                       #337.64
        xor       ebp, ebp                                      #24.32
        xor       r9d, r9d                                      #21.32
        mov       QWORD PTR [152+rsp], r12                      #337.64[spill]
        mov       rax, 0x0ffffffff                              #26.32
        adcx      r12, r12                                      #21.32
        vpxor     xmm0, xmm0, xmm0                              #338.20
        mov       r11, QWORD PTR [40+rsp]                       #337.88
        mov       r9, r12                                       #25.32
        mov       QWORD PTR [160+rsp], r11                      #337.88[spill]
        mov       r13, 0xffffffff00000001                       #28.32
        adcx      r11, r11                                      #22.32
        mov       r10, QWORD PTR [48+rsp]                       #337.80
        mov       QWORD PTR [168+rsp], r10                      #337.80[spill]
        adcx      r10, r10                                      #23.32
        mov       r8, QWORD PTR [56+rsp]                        #337.72
        mov       QWORD PTR [176+rsp], r8                       #337.72[spill]
        adcx      r8, r8                                        #24.32
        mov       rcx, r8                                       #28.32
        setb      bpl                                           #24.32
        mov       rbx, -1                                       #24.32
        xor       r14d, r14d                                    #24.32
        xor       r15d, r15d                                    #24.32
        sub       r9, rbx                                       #25.32
        mov       rbx, r11                                      #26.32
        sbb       rbx, rax                                      #26.32
        mov       rax, r10                                      #27.32
        sbb       rax, r14                                      #27.32
        sbb       rcx, r13                                      #28.32
        sbb       rbp, r14                                      #29.30
        setb      r15b                                          #29.30
        dec       r15                                           #9.35
        and       rcx, r15                                      #10.31
        and       rax, r15                                      #10.31
        and       rbx, r15                                      #10.31
        and       r9, r15                                       #10.31
        not       r15                                           #10.43
        and       r8, r15                                       #10.60
        and       r10, r15                                      #10.60
        and       r11, r15                                      #10.60
        and       r15, r12                                      #10.60
        or        rcx, r8                                       #10.60
        or        rax, r10                                      #10.60
        or        rbx, r11                                      #10.60
        or        r9, r15                                       #10.60
        mov       QWORD PTR [64+rsp], rcx                       #337.35
        mov       QWORD PTR [72+rsp], rax                       #337.35
        mov       QWORD PTR [80+rsp], rbx                       #337.35
        mov       QWORD PTR [88+rsp], r9                        #337.35
        vmovups   XMMWORD PTR [rsp], xmm0                       #338.20
        vmovups   XMMWORD PTR [16+rsp], xmm0                    #338.20
        mov       r8, QWORD PTR [312+rsp]                       #41.32[spill]
        xor       ebp, ebp                                      #41.32
        sub       r8, rcx                                       #41.32
        mov       rcx, 0xffffffff00000001                       #49.30
        sbb       rdx, rax                                      #42.32
        sbb       rsi, rbx                                      #43.32
        sbb       rdi, r9                                       #44.32
        mov       r9d, ebp                                      #44.32
        vpxor     xmm0, xmm0, xmm0                              #348.21
        setb      r9b                                           #44.32
        xor       r10d, r10d                                    #44.32
        xor       r12d, r12d                                    #44.32
        xor       r15d, r15d                                    #44.32
        xor       eax, eax                                      #44.32
        xor       ebx, ebx                                      #44.32
        xor       r13d, r13d                                    #44.32
        test      r9d, r9d                                      #45.38
        mov       r9, -1                                        #45.38
        cmovne    r13, r9                                       #45.38
        adox      r10d, ebp                                     #46.32
        mov       r11d, r13d                                    #47.32
        adox      r8, r13                                       #46.32
        mov       QWORD PTR [24+rsp], r8                        #338.34
        adox      rdx, r11                                      #47.32
        mov       QWORD PTR [16+rsp], rdx                       #338.34
        adox      rsi, rbx                                      #48.32
        mov       QWORD PTR [8+rsp], rsi                        #338.34
        seto      r12b                                          #48.32
        and       r13, rcx                                      #49.30
        cmp       ebp, r12d                                     #49.30
        mov       r11, QWORD PTR [240+rsp]                      #10.31[spill]
        adcx      rdi, r13                                      #49.30
        mov       QWORD PTR [rsp], rdi                          #338.34
        sub       rdi, QWORD PTR [320+rsp]                      #41.32[spill]
        sbb       rsi, QWORD PTR [344+rsp]                      #42.32[spill]
        sbb       rdx, QWORD PTR [336+rsp]                      #43.32[spill]
        sbb       r8, QWORD PTR [328+rsp]                       #44.32[spill]
        setb      r15b                                          #44.32
        test      r15d, r15d                                    #45.38
        mov       r15, QWORD PTR [96+rsp]                       #340.32[spill]
        cmove     r9, rbx                                       #45.38
        adox      eax, ebp                                      #46.32
        mov       r10d, r9d                                     #47.32
        adox      rdi, r9                                       #46.32
        mov       rax, QWORD PTR [104+rsp]                      #53.1[spill]
        adox      rsi, r10                                      #47.32
        mov       QWORD PTR [24+rax], rdi                       #53.1
        adox      rdx, rbx                                      #48.32
        mov       ebx, ebp                                      #48.32
        mov       QWORD PTR [8+rax], rdx                        #51.1
        seto      bl                                            #48.32
        and       rcx, r9                                       #49.30
        cmp       ebp, ebx                                      #49.30
        mov       QWORD PTR [16+rax], rsi                       #52.1
        adcx      r8, rcx                                       #49.30
        mov       QWORD PTR [rax], r8                           #50.1
        mov       r12, QWORD PTR [24+r15]                       #340.32
        mov       rcx, QWORD PTR [224+rsp]                      #10.60[spill]
        and       rdi, r11                                      #10.31
        and       r12, rcx                                      #10.60
        and       rsi, r11                                      #10.31
        or        rdi, r12                                      #10.60
        and       rdx, r11                                      #10.31
        mov       QWORD PTR [24+rax], rdi                       #340.5
        and       r8, r11                                       #10.31
        mov       r13, QWORD PTR [16+r15]                       #341.32
        and       r13, rcx                                      #10.60
        or        rsi, r13                                      #10.60
        mov       QWORD PTR [16+rax], rsi                       #341.5
        mov       r14, QWORD PTR [8+r15]                        #342.32
        and       r14, rcx                                      #10.60
        or        rdx, r14                                      #10.60
        mov       QWORD PTR [8+rax], rdx                        #342.5
        mov       r11, QWORD PTR [112+rsp]                      #344.32[spill]
        mov       r13, QWORD PTR [r15]                          #343.32
        and       r13, rcx                                      #10.60
        or        r8, r13                                       #10.60
        mov       QWORD PTR [rax], r8                           #343.5
        mov       rbx, QWORD PTR [232+rsp]                      #10.31[spill]
        and       rdi, rbx                                      #10.31
        mov       r12, QWORD PTR [216+rsp]                      #10.60[spill]
        and       rsi, rbx                                      #10.31
        mov       rbp, QWORD PTR [24+r11]                       #344.32
        and       rdx, rbx                                      #10.31
        and       rbp, r12                                      #10.60
        and       r8, rbx                                       #10.31
        or        rdi, rbp                                      #10.60
        mov       QWORD PTR [24+rax], rdi                       #344.5
        mov       r9, QWORD PTR [16+r11]                        #345.32
        and       r9, r12                                       #10.60
        or        rsi, r9                                       #10.60
        mov       QWORD PTR [16+rax], rsi                       #345.5
        mov       r10, QWORD PTR [8+r11]                        #346.32
        and       r10, r12                                      #10.60
        or        rdx, r10                                      #10.60
        mov       QWORD PTR [8+rax], rdx                        #346.5
        mov       rcx, QWORD PTR [r11]                          #347.32
        and       rcx, r12                                      #10.60
        or        r8, rcx                                       #10.60
        mov       QWORD PTR [312+rsp], r8                       #10.60[spill]
        mov       QWORD PTR [rax], r8                           #347.5
        vmovups   XMMWORD PTR [32+rsp], xmm0                    #348.21
        vmovups   XMMWORD PTR [48+rsp], xmm0                    #348.21
        mov       rbp, r11                                      #73.33
        xor       r8d, r8d                                      #77.32
        mov       QWORD PTR [368+rsp], rdx                      #[spill]
        xor       r10d, r10d                                    #77.32
        mov       rdx, QWORD PTR [320+rsp]                      #73.33[spill]
        mov       QWORD PTR [352+rsp], rdi                      #[spill]
        mov       r13, 0x0ffffffff                              #82.33
        mulx      rax, rdi, QWORD PTR [32+rbp]                  #73.33
        mov       r14, 0xffffffff00000001                       #83.33
        mulx      rbx, r9, QWORD PTR [40+rbp]                   #74.33
        adox      rdi, rbx                                      #77.32
        vpxor     xmm0, xmm0, xmm0                              #349.21
        mulx      rcx, r11, QWORD PTR [48+rbp]                  #75.33
        adox      r9, rcx                                       #78.32
        mulx      r12, r15, QWORD PTR [56+rbp]                  #76.33
        mov       rdx, rax                                      #81.33
        adox      r11, r12                                      #79.32
        mov       QWORD PTR [360+rsp], rsi                      #[spill]
        seto      r10b                                          #79.32
        clc                                                     #80.30
        adcx      r10, r15                                      #80.30
        mulx      r12, rcx, r13                                 #82.33
        mov       rsi, -1                                       #81.33
        mulx      r15, rbx, rsi                                 #81.33
        mulx      r13, r14, r14                                 #83.33
        mov       edx, r8d                                      #84.32
        adox      edx, r8d                                      #84.32
        mov       edx, r8d                                      #86.32
        adox      rbx, r12                                      #84.32
        mov       r12d, 0                                       #85.32
        adox      rcx, r12                                      #85.32
        adox      r13, r12                                      #86.32
        seto      dl                                            #86.32
        clc                                                     #87.30
        adcx      rdx, r14                                      #87.30
        mov       r14d, r8d                                     #88.30
        adox      r14d, r8d                                     #88.30
        adox      rax, r15                                      #88.30
        adox      rdi, rbx                                      #89.32
        mov       ebx, r8d                                      #92.32
        adox      r9, rcx                                       #90.32
        adox      r11, r13                                      #91.32
        adox      r10, rdx                                      #92.32
        mov       rdx, QWORD PTR [344+rsp]                      #93.33[spill]
        seto      bl                                            #92.32
        clc                                                     #97.32
        mulx      r15, r13, QWORD PTR [32+rbp]                  #93.33
        mulx      rcx, r14, QWORD PTR [40+rbp]                  #94.33
        adcx      r13, rcx                                      #97.32
        mulx      rax, rcx, QWORD PTR [48+rbp]                  #95.33
        adcx      r14, rax                                      #98.32
        mulx      rax, rbp, QWORD PTR [56+rbp]                  #96.33
        mov       edx, r8d                                      #100.30
        adcx      rcx, rax                                      #99.32
        mov       eax, r8d                                      #99.32
        setb      al                                            #99.32
        adox      edx, r8d                                      #100.30
        adox      rax, rbp                                      #100.30
        mov       ebp, r8d                                      #100.30
        seto      bpl                                           #100.30
        clc                                                     #101.34
        adcx      rdi, r15                                      #101.34
        mov       r15, 0x0ffffffff                              #107.35
        mov       rdx, rdi                                      #106.35
        adcx      r9, r13                                       #102.34
        mov       r13, 0xffffffff00000001                       #108.35
        mulx      rbp, rsi, rsi                                 #106.35
        adcx      r11, r14                                      #103.34
        mulx      r13, r14, r13                                 #108.35
        adcx      r10, rcx                                      #104.34
        mov       ecx, r8d                                      #105.34
        adcx      rbx, rax                                      #105.34
        mulx      r15, rax, r15                                 #107.35
        mov       edx, r8d                                      #109.34
        setb      cl                                            #105.34
        adox      edx, r8d                                      #109.34
        mov       rdx, QWORD PTR [336+rsp]                      #119.35[spill]
        adox      rsi, r15                                      #109.34
        mov       r15d, r8d                                     #111.34
        adox      rax, r12                                      #110.34
        adox      r13, r12                                      #111.34
        seto      r15b                                          #111.34
        clc                                                     #112.31
        adcx      r15, r14                                      #112.31
        mov       r14d, r8d                                     #113.31
        adox      r14d, r8d                                     #113.31
        adox      rdi, rbp                                      #113.31
        mov       edi, r8d                                      #117.34
        adox      r9, rsi                                       #114.34
        adox      r11, rax                                      #115.34
        adox      r10, r13                                      #116.34
        mov       r13, QWORD PTR [112+rsp]                      #119.35[spill]
        adox      rbx, r15                                      #117.34
        mulx      rax, rsi, QWORD PTR [32+r13]                  #119.35
        seto      dil                                           #117.34
        clc                                                     #123.34
        mulx      rbp, r15, QWORD PTR [40+r13]                  #120.35
        adcx      rsi, rbp                                      #123.34
        mulx      r14, rbp, QWORD PTR [48+r13]                  #121.35
        adcx      r15, r14                                      #124.34
        mulx      r13, r14, QWORD PTR [56+r13]                  #122.35
        mov       edx, r8d                                      #126.31
        adcx      rbp, r13                                      #125.34
        mov       r13d, r8d                                     #125.34
        setb      r13b                                          #125.34
        adox      edx, r8d                                      #126.31
        adox      r13, r14                                      #126.31
        clc                                                     #127.34
        adcx      r9, rax                                       #127.34
        mov       rdx, r9                                       #132.35
        adcx      r11, rsi                                      #128.34
        mov       esi, r8d                                      #130.34
        adcx      r10, r15                                      #129.34
        adcx      rbx, rbp                                      #130.34
        mov       rbp, 0x0ffffffff                              #133.35
        mulx      r15, r14, rbp                                 #133.35
        setb      sil                                           #130.34
        xor       eax, eax                                      #130.34
        add       ecx, edi                                      #131.34
        mov       rdi, -1                                       #131.34
        cmp       r8d, esi                                      #131.34
        mov       rsi, 0xffffffff00000001                       #134.35
        adcx      rcx, r13                                      #131.34
        mulx      rdi, r13, rdi                                 #132.35
        mulx      rsi, rbp, rsi                                 #134.35
        mov       edx, r8d                                      #135.34
        setb      al                                            #131.34
        adox      edx, r8d                                      #135.34
        mov       rdx, QWORD PTR [328+rsp]                      #145.35[spill]
        adox      r13, r15                                      #135.34
        mov       r15d, r8d                                     #137.34
        adox      r14, r12                                      #136.34
        adox      rsi, r12                                      #137.34
        seto      r15b                                          #137.34
        clc                                                     #138.31
        adcx      r15, rbp                                      #138.31
        mov       ebp, r8d                                      #139.31
        adox      ebp, r8d                                      #139.31
        mov       rbp, QWORD PTR [112+rsp]                      #145.35[spill]
        adox      r9, rdi                                       #139.31
        mov       r9d, r8d                                      #143.34
        adox      r11, r13                                      #140.34
        mulx      rdi, r13, QWORD PTR [32+rbp]                  #145.35
        adox      r10, r14                                      #141.34
        adox      rbx, rsi                                      #142.34
        adox      rcx, r15                                      #143.34
        mulx      r15, rsi, QWORD PTR [40+rbp]                  #146.35
        seto      r9b                                           #143.34
        clc                                                     #149.34
        adcx      r13, r15                                      #149.34
        mulx      r15, r14, QWORD PTR [48+rbp]                  #147.35
        adcx      rsi, r15                                      #150.34
        mulx      rbp, r15, QWORD PTR [56+rbp]                  #148.35
        mov       edx, r8d                                      #152.31
        adcx      r14, rbp                                      #151.34
        mov       ebp, r8d                                      #151.34
        setb      bpl                                           #151.34
        adox      edx, r8d                                      #152.31
        adox      rbp, r15                                      #152.31
        clc                                                     #153.34
        adcx      r11, rdi                                      #153.34
        mov       rdx, r11                                      #158.35
        adcx      r10, r13                                      #154.34
        mov       r13d, r8d                                     #156.34
        adcx      rbx, rsi                                      #155.34
        mov       rsi, 0xffffffff00000001                       #160.35
        adcx      rcx, r14                                      #156.34
        mov       r14, 0x0ffffffff                              #159.35
        setb      r13b                                          #156.34
        xor       edi, edi                                      #156.34
        add       eax, r9d                                      #157.34
        mov       r9, -1                                        #157.34
        cmp       r8d, r13d                                     #157.34
        mulx      r9, r15, r9                                   #158.35
        adcx      rax, rbp                                      #157.34
        mulx      r13, rbp, r14                                 #159.35
        mulx      rsi, r14, rsi                                 #160.35
        mov       edx, r8d                                      #161.34
        setb      dil                                           #157.34
        adox      edx, r8d                                      #161.34
        mov       rdx, 0xffffffff00000001                       #174.34
        adox      r15, r13                                      #161.34
        mov       r13d, r8d                                     #163.34
        adox      rbp, r12                                      #162.34
        adox      rsi, r12                                      #163.34
        seto      r13b                                          #163.34
        clc                                                     #164.31
        adcx      r13, r14                                      #164.31
        mov       r14d, r8d                                     #165.31
        adox      r14d, r8d                                     #165.31
        adox      r11, r9                                       #165.31
        mov       r11d, r8d                                     #169.34
        adox      r10, r15                                      #166.34
        adox      rbx, rbp                                      #167.34
        mov       rbp, 0x0ffffffff                              #172.34
        adox      rcx, rsi                                      #168.34
        adox      rax, r13                                      #169.34
        mov       rsi, rax                                      #174.34
        seto      r11b                                          #169.34
        mov       r9, -1                                        #169.34
        xor       r15d, r15d                                    #169.34
        add       edi, r11d                                     #175.31
        mov       r11, r10                                      #171.34
        sub       r11, r9                                       #171.34
        mov       r9, rbx                                       #172.34
        sbb       r9, rbp                                       #172.34
        mov       rbp, rcx                                      #173.34
        sbb       rbp, r12                                      #173.34
        sbb       rsi, rdx                                      #174.34
        setb      r15b                                          #174.34
        cmp       r8d, r15d                                     #175.31
        sbb       rdi, r12                                      #175.31
        setb      r8b                                           #175.31
        dec       r8                                            #9.35
        and       rsi, r8                                       #10.31
        and       rbp, r8                                       #10.31
        and       r9, r8                                        #10.31
        and       r11, r8                                       #10.31
        not       r8                                            #10.43
        and       rax, r8                                       #10.60
        and       rcx, r8                                       #10.60
        and       rbx, r8                                       #10.60
        and       r8, r10                                       #10.60
        or        rsi, rax                                      #10.60
        or        rbp, rcx                                      #10.60
        or        r9, rbx                                       #10.60
        or        r11, r8                                       #10.60
        mov       QWORD PTR [64+rsp], rsi                       #10.60[spill]
        mov       QWORD PTR [32+rsp], rsi                       #348.34
        mov       QWORD PTR [40+rsp], rbp                       #348.34
        mov       QWORD PTR [72+rsp], r11                       #10.60[spill]
        mov       QWORD PTR [48+rsp], r9                        #348.34
        mov       QWORD PTR [56+rsp], r11                       #348.34
        vmovups   XMMWORD PTR [rsp], xmm0                       #349.21
        vmovups   XMMWORD PTR [16+rsp], xmm0                    #349.21
        mov       rdx, QWORD PTR [368+rsp]                      #349.21[spill]
        mov       rsi, QWORD PTR [360+rsp]                      #349.21[spill]
        mov       rdi, QWORD PTR [352+rsp]                      #349.21[spill]
        mov       rax, QWORD PTR [152+rsp]                      #41.32[spill]
        xor       r12d, r12d                                    #41.32
        sub       rax, QWORD PTR [312+rsp]                      #41.32[spill]
        mov       rbx, QWORD PTR [160+rsp]                      #42.32[spill]
        sbb       rbx, rdx                                      #42.32
        mov       rcx, QWORD PTR [168+rsp]                      #43.32[spill]
        mov       r11, 0xffffffff00000001                       #49.30
        sbb       rcx, rsi                                      #43.32
        mov       r13, QWORD PTR [176+rsp]                      #44.32[spill]
        vpxor     xmm0, xmm0, xmm0                              #350.21
        sbb       r13, rdi                                      #44.32
        mov       edi, r12d                                     #44.32
        setb      dil                                           #44.32
        mov       r8, -1                                        #44.32
        xor       r10d, r10d                                    #44.32
        xor       edx, edx                                      #44.32
        test      edi, edi                                      #45.38
        cmove     r8, rdx                                       #45.38
        clc                                                     #46.32
        mov       esi, r8d                                      #47.32
        adcx      rax, r8                                       #46.32
        mov       QWORD PTR [152+rsp], rax                      #46.32[spill]
        adcx      rbx, rsi                                      #47.32
        mov       QWORD PTR [24+rsp], rax                       #349.34
        adcx      rcx, rdx                                      #48.32
        mov       QWORD PTR [160+rsp], rbx                      #47.32[spill]
        setb      r10b                                          #48.32
        and       r11, r8                                       #49.30
        cmp       r12d, r10d                                    #49.30
        mov       QWORD PTR [168+rsp], rcx                      #48.32[spill]
        adcx      r13, r11                                      #49.30
        mov       QWORD PTR [8+rsp], rcx                        #349.34
        mov       QWORD PTR [16+rsp], rbx                       #349.34
        mov       QWORD PTR [176+rsp], r13                      #49.30[spill]
        mov       QWORD PTR [rsp], r13                          #349.34
        vmovups   XMMWORD PTR [32+rsp], xmm0                    #350.21
        vmovups   XMMWORD PTR [48+rsp], xmm0                    #350.21
        mov       rdx, r13                                      #73.33
        mov       QWORD PTR [rsp], rbp                          #[spill]
        mov       r14, -1                                       #81.33
        xor       r13d, r13d                                    #77.32
        mov       r12, 0x0ffffffff                              #82.33
        mov       r13, 0xffffffff00000001                       #83.33
        mov       r8, QWORD PTR [144+rsp]                       #73.33[spill]
        mov       rbp, QWORD PTR [128+rsp]                      #74.33[spill]
        mov       QWORD PTR [8+rsp], r9                         #[spill]
        mulx      rax, rbx, r8                                  #73.33
        mulx      r9, r11, rbp                                  #74.33
        adox      rbx, r9                                       #77.32
        mulx      rsi, rdi, QWORD PTR [136+rsp]                 #75.33[spill]
        adox      r11, rsi                                      #78.32
        mov       esi, 0                                        #79.32
        mulx      r15, r10, QWORD PTR [120+rsp]                 #76.33[spill]
        mov       r9d, esi                                      #79.32
        adox      rdi, r15                                      #79.32
        mov       rdx, rax                                      #81.33
        seto      r9b                                           #79.32
        clc                                                     #80.30
        adcx      r9, r10                                       #80.30
        mulx      r14, r15, r14                                 #81.33
        mulx      r10, rcx, r12                                 #82.33
        mulx      r12, r13, r13                                 #83.33
        mov       edx, esi                                      #84.32
        adox      edx, esi                                      #84.32
        mov       edx, esi                                      #86.32
        adox      r15, r10                                      #84.32
        mov       r10d, 0                                       #85.32
        adox      rcx, r10                                      #85.32
        adox      r12, r10                                      #86.32
        seto      dl                                            #86.32
        clc                                                     #87.30
        adcx      rdx, r13                                      #87.30
        mov       r13d, esi                                     #88.30
        adox      r13d, esi                                     #88.30
        adox      rax, r14                                      #88.30
        adox      rbx, r15                                      #89.32
        adox      r11, rcx                                      #90.32
        mov       ecx, esi                                      #92.32
        adox      rdi, r12                                      #91.32
        adox      r9, rdx                                       #92.32
        mov       rdx, QWORD PTR [168+rsp]                      #93.33[spill]
        seto      cl                                            #92.32
        clc                                                     #97.32
        mulx      r15, r12, r8                                  #93.33
        mulx      rax, r14, rbp                                 #94.33
        adcx      r12, rax                                      #97.32
        mulx      r13, rbp, QWORD PTR [136+rsp]                 #95.33[spill]
        adcx      r14, r13                                      #98.32
        mulx      r13, rax, QWORD PTR [120+rsp]                 #96.33[spill]
        mov       edx, esi                                      #100.30
        adcx      rbp, r13                                      #99.32
        mov       r13d, esi                                     #99.32
        setb      r13b                                          #99.32
        adox      edx, esi                                      #100.30
        adox      r13, rax                                      #100.30
        mov       eax, esi                                      #100.30
        seto      al                                            #100.30
        clc                                                     #101.34
        adcx      rbx, r15                                      #101.34
        mov       r15, 0x0ffffffff                              #107.35
        mov       rdx, rbx                                      #106.35
        adcx      r11, r12                                      #102.34
        adcx      rdi, r14                                      #103.34
        mulx      r15, r14, r15                                 #107.35
        adcx      r9, rbp                                       #104.34
        mov       ebp, esi                                      #105.34
        adcx      rcx, r13                                      #105.34
        mov       r13, -1                                       #106.35
        mulx      rax, r13, r13                                 #106.35
        setb      bpl                                           #105.34
        mov       DWORD PTR [16+rsp], ebp                       #105.34[spill]
        mov       rbp, 0xffffffff00000001                       #108.35
        mulx      rbp, r12, rbp                                 #108.35
        mov       edx, esi                                      #109.34
        adox      edx, esi                                      #109.34
        mov       rdx, QWORD PTR [160+rsp]                      #119.35[spill]
        adox      r13, r15                                      #109.34
        mov       r15d, esi                                     #111.34
        adox      r14, r10                                      #110.34
        adox      rbp, r10                                      #111.34
        seto      r15b                                          #111.34
        clc                                                     #112.31
        adcx      r15, r12                                      #112.31
        mov       r12d, esi                                     #113.31
        adox      r12d, esi                                     #113.31
        adox      rbx, rax                                      #113.31
        mulx      rbx, r12, QWORD PTR [128+rsp]                 #120.35[spill]
        adox      r11, r13                                      #114.34
        adox      rdi, r14                                      #115.34
        adox      r9, rbp                                       #116.34
        mov       ebp, esi                                      #117.34
        adox      rcx, r15                                      #117.34
        mulx      r15, r14, r8                                  #119.35
        seto      bpl                                           #117.34
        clc                                                     #123.34
        adcx      r14, rbx                                      #123.34
        mulx      rax, rbx, QWORD PTR [136+rsp]                 #121.35[spill]
        adcx      r12, rax                                      #124.34
        mulx      r13, rax, QWORD PTR [120+rsp]                 #122.35[spill]
        mov       edx, esi                                      #126.31
        adcx      rbx, r13                                      #125.34
        mov       r13d, esi                                     #125.34
        setb      r13b                                          #125.34
        adox      edx, esi                                      #126.31
        adox      r13, rax                                      #126.31
        clc                                                     #127.34
        mov       eax, DWORD PTR [16+rsp]                       #131.34[spill]
        adcx      r11, r15                                      #127.34
        mov       r15d, esi                                     #130.34
        mov       rdx, r11                                      #132.35
        adcx      rdi, r14                                      #128.34
        adcx      r9, r12                                       #129.34
        adcx      rcx, rbx                                      #130.34
        setb      r15b                                          #130.34
        xor       r14d, r14d                                    #130.34
        mov       rbx, -1                                       #130.34
        add       eax, ebp                                      #131.34
        cmp       esi, r15d                                     #131.34
        mov       r15, 0x0ffffffff                              #133.35
        mov       rbp, 0xffffffff00000001                       #134.35
        adcx      rax, r13                                      #131.34
        mulx      r13, rbx, rbx                                 #132.35
        setb      r14b                                          #131.34
        mov       DWORD PTR [24+rsp], r14d                      #131.34[spill]
        mulx      r15, r14, r15                                 #133.35
        mulx      rbp, r12, rbp                                 #134.35
        mov       edx, esi                                      #135.34
        adox      edx, esi                                      #135.34
        mov       rdx, QWORD PTR [152+rsp]                      #145.35[spill]
        adox      rbx, r15                                      #135.34
        mov       r15d, esi                                     #137.34
        adox      r14, r10                                      #136.34
        adox      rbp, r10                                      #137.34
        seto      r15b                                          #137.34
        clc                                                     #138.31
        adcx      r15, r12                                      #138.31
        mov       r12d, esi                                     #139.31
        adox      r12d, esi                                     #139.31
        mov       r12d, esi                                     #152.31
        adox      r11, r13                                      #139.31
        adox      rdi, rbx                                      #140.34
        mulx      rbx, r8, r8                                   #145.35
        adox      r9, r14                                       #141.34
        mulx      r14, r13, QWORD PTR [136+rsp]                 #147.35[spill]
        adox      rcx, rbp                                      #142.34
        mov       ebp, esi                                      #143.34
        adox      rax, r15                                      #143.34
        mulx      r11, r15, QWORD PTR [128+rsp]                 #146.35[spill]
        seto      bpl                                           #143.34
        clc                                                     #149.34
        adcx      r8, r11                                       #149.34
        adcx      r15, r14                                      #150.34
        mulx      r11, r14, QWORD PTR [120+rsp]                 #148.35[spill]
        adcx      r13, r11                                      #151.34
        mov       r11d, esi                                     #151.34
        setb      r11b                                          #151.34
        adox      r12d, esi                                     #152.31
        adox      r11, r14                                      #152.31
        clc                                                     #153.34
        mov       r14d, DWORD PTR [24+rsp]                      #157.34[spill]
        adcx      rdi, rbx                                      #153.34
        mov       rdx, rdi                                      #158.35
        adcx      r9, r8                                        #154.34
        mov       r8d, esi                                      #156.34
        adcx      rcx, r15                                      #155.34
        mov       r15, 0xffffffff00000001                       #160.35
        adcx      rax, r13                                      #156.34
        setb      r8b                                           #156.34
        mov       r13, -1                                       #156.34
        add       r14d, ebp                                     #157.34
        cmp       esi, r8d                                      #157.34
        mov       rbp, 0x0ffffffff                              #159.35
        mulx      rbx, r8, r13                                  #158.35
        adcx      r14, r11                                      #157.34
        mov       r11d, esi                                     #157.34
        mulx      r12, r13, rbp                                 #159.35
        mulx      rbp, r15, r15                                 #160.35
        mov       edx, esi                                      #161.34
        setb      r11b                                          #157.34
        adox      edx, esi                                      #161.34
        adox      r8, r12                                       #161.34
        mov       r12d, esi                                     #163.34
        adox      r13, r10                                      #162.34
        adox      rbp, r10                                      #163.34
        seto      r12b                                          #163.34
        clc                                                     #164.31
        adcx      r12, r15                                      #164.31
        mov       r15d, esi                                     #165.31
        adox      r15d, esi                                     #165.31
        adox      rdi, rbx                                      #165.31
        mov       rbx, 0x0ffffffff                              #172.34
        mov       edi, esi                                      #169.34
        adox      r9, r8                                        #166.34
        mov       r15, r9                                       #171.34
        adox      rcx, r13                                      #167.34
        mov       r13, rcx                                      #172.34
        adox      rax, rbp                                      #168.34
        adox      r14, r12                                      #169.34
        mov       r8, r14                                       #174.34
        seto      dil                                           #169.34
        mov       rdx, -1                                       #169.34
        xor       ebp, ebp                                      #169.34
        add       r11d, edi                                     #175.31
        sub       r15, rdx                                      #171.34
        mov       rdi, 0xffffffff00000001                       #174.34
        sbb       r13, rbx                                      #172.34
        mov       rbx, rax                                      #173.34
        sbb       rbx, r10                                      #173.34
        sbb       r8, rdi                                       #174.34
        setb      bpl                                           #174.34
        cmp       esi, ebp                                      #175.31
        mov       ebp, esi                                      #175.31
        sbb       r11, r10                                      #175.31
        setb      bpl                                           #175.31
        dec       rbp                                           #9.35
        and       r8, rbp                                       #10.31
        and       rbx, rbp                                      #10.31
        and       r13, rbp                                      #10.31
        and       r15, rbp                                      #10.31
        not       rbp                                           #10.43
        and       r14, rbp                                      #10.60
        and       rax, rbp                                      #10.60
        or        r8, r14                                       #10.60
        and       rcx, rbp                                      #10.60
        and       rbp, r9                                       #10.60
        or        rbx, rax                                      #10.60
        mov       QWORD PTR [32+rsp], r8                        #350.34
        or        r13, rcx                                      #10.60
        or        r15, rbp                                      #10.60
        xor       r9d, r9d                                      #44.32
        sub       r8, QWORD PTR [64+rsp]                        #41.32[spill]
        mov       QWORD PTR [40+rsp], rbx                       #350.34
        sbb       rbx, QWORD PTR [rsp]                          #42.32[spill]
        mov       QWORD PTR [48+rsp], r13                       #350.34
        sbb       r13, QWORD PTR [8+rsp]                        #43.32[spill]
        mov       QWORD PTR [56+rsp], r15                       #350.34
        sbb       r15, QWORD PTR [72+rsp]                       #44.32[spill]
        setb      r9b                                           #44.32
        xor       ecx, ecx                                      #44.32
        test      r9d, r9d                                      #45.38
        mov       r9, QWORD PTR [104+rsp]                       #53.1[spill]
        cmove     rdx, r10                                      #45.38
        clc                                                     #46.32
        mov       eax, edx                                      #47.32
        adcx      r8, rdx                                       #46.32
        mov       QWORD PTR [56+r9], r8                         #53.1
        adcx      rbx, rax                                      #47.32
        mov       QWORD PTR [48+r9], rbx                        #52.1
        adcx      r13, r10                                      #48.32
        mov       QWORD PTR [40+r9], r13                        #51.1
        setb      cl                                            #48.32
        and       rdi, rdx                                      #49.30
        cmp       esi, ecx                                      #49.30
        mov       rax, QWORD PTR [224+rsp]                      #10.60[spill]
        adcx      r15, rdi                                      #49.30
        mov       QWORD PTR [32+r9], r15                        #50.1
        mov       rsi, QWORD PTR [240+rsp]                      #10.31[spill]
        and       r8, rsi                                       #10.31
        and       rbx, rsi                                      #10.31
        and       r13, rsi                                      #10.31
        and       rsi, r15                                      #10.31
        mov       r15, QWORD PTR [96+rsp]                       #352.32[spill]
        mov       rcx, QWORD PTR [232+rsp]                      #10.31[spill]
        mov       rdx, QWORD PTR [216+rsp]                      #10.60[spill]
        mov       r10, QWORD PTR [56+r15]                       #352.32
        and       r10, rax                                      #10.60
        or        r8, r10                                       #10.60
        mov       QWORD PTR [56+r9], r8                         #352.5
        and       r8, rcx                                       #10.31
        mov       r12, QWORD PTR [48+r15]                       #353.32
        and       r12, rax                                      #10.60
        or        rbx, r12                                      #10.60
        mov       QWORD PTR [48+r9], rbx                        #353.5
        and       rbx, rcx                                      #10.31
        mov       r14, QWORD PTR [40+r15]                       #354.32
        and       r14, rax                                      #10.60
        or        r13, r14                                      #10.60
        mov       QWORD PTR [40+r9], r13                        #354.5
        and       r13, rcx                                      #10.31
        mov       r14, QWORD PTR [112+rsp]                      #356.32[spill]
        and       rax, QWORD PTR [32+r15]                       #10.60
        or        rsi, rax                                      #10.60
        mov       QWORD PTR [32+r9], rsi                        #355.5
        and       rcx, rsi                                      #10.31
        mov       r12, QWORD PTR [56+r14]                       #356.32
        and       r12, rdx                                      #10.60
        or        r8, r12                                       #10.60
        mov       QWORD PTR [56+r9], r8                         #356.5
        mov       r8, QWORD PTR [48+r14]                        #357.32
        and       r8, rdx                                       #10.60
        or        rbx, r8                                       #10.60
        mov       QWORD PTR [48+r9], rbx                        #357.5
        mov       rbx, QWORD PTR [40+r14]                       #358.32
        and       rbx, rdx                                      #10.60
        or        r13, rbx                                      #10.60
        mov       QWORD PTR [40+r9], r13                        #358.5
        and       rdx, QWORD PTR [32+r14]                       #10.60
        or        rcx, rdx                                      #10.60
        mov       QWORD PTR [32+r9], rcx                        #359.5
        add       rsp, 424                                      #360.1
        pop       rbp                                           #360.1
        pop       rbx                                           #360.1
        pop       r15                                           #360.1
        pop       r14                                           #360.1
        pop       r13                                           #360.1
        pop       r12                                           #360.1
        ret                                                     #360.1
