.intel_syntax noprefix
.section .text
.globl p256_jacobian_add_affine
.type p256_jacobian_add_affine, @function
p256_jacobian_add_affine:
        push      rbx                                           #187.3
        mov       rbx, rsp                                      #187.3
        and       rsp, -32                                      #187.3
        push      rbp                                           #187.3
        push      rbp                                           #187.3
        mov       rbp, QWORD PTR [8+rbx]                        #187.3
        mov       QWORD PTR [8+rsp], rbp                        #187.3
        mov       rbp, rsp                                      #187.3
        push      r12                                           #187.3
        push      r13                                           #187.3
        push      r14                                           #187.3
        push      r15                                           #187.3
        sub       rsp, 304                                      #187.3
        vpxor     ymm0, ymm0, ymm0                              #196.20
        mov       QWORD PTR [-104+rbp], rdx                     #187.3[spill]
        mov       QWORD PTR [-88+rbp], rsi                      #187.3[spill]
        mov       QWORD PTR [-96+rbp], rdi                      #187.3[spill]
        vmovups   YMMWORD PTR [-240+rbp], ymm0                  #196.20
        xor       r13d, r13d                                    #42.32
        xor       eax, eax                                      #42.32
        xor       r9d, r9d                                      #42.32
        mov       rdx, QWORD PTR [64+rsi]                       #38.33
        mulx      r12, r15, QWORD PTR [64+rsi]                  #38.33
        mulx      r10, rdi, QWORD PTR [72+rsi]                  #39.33
        adcx      r15, r10                                      #42.32
        mov       r10, -1                                       #46.33
        mulx      r14, r8, QWORD PTR [80+rsi]                   #40.33
        adcx      rdi, r14                                      #43.32
        mov       r14, 0x0ffffffff                              #47.33
        mulx      rcx, r11, QWORD PTR [88+rsi]                  #41.33
        mov       esi, 0                                        #42.32
        adcx      r8, rcx                                       #44.32
        setb      r13b                                          #44.32
        mov       rdx, r12                                      #46.33
        adox      eax, esi                                      #45.30
        adox      r13, r11                                      #45.30
        mulx      rax, r11, r10                                 #46.33
        mov       r10, 0xffffffff00000001                       #48.33
        seto      r9b                                           #45.30
        clc                                                     #49.32
        mulx      r9, rcx, r14                                  #47.33
        adcx      r11, r9                                       #49.32
        mulx      r14, r9, r10                                  #48.33
        mov       r10d, 0                                       #50.32
        adcx      rcx, r10                                      #50.32
        mov       edx, esi                                      #52.30
        adcx      r14, r10                                      #51.32
        mov       r10d, esi                                     #51.32
        setb      r10b                                          #51.32
        adox      edx, esi                                      #52.30
        adox      r10, r9                                       #52.30
        clc                                                     #53.30
        adcx      r12, rax                                      #53.30
        adcx      r15, r11                                      #54.32
        adcx      rdi, rcx                                      #55.32
        mov       ecx, esi                                      #57.32
        adcx      r8, r14                                       #56.32
        mov       r14, QWORD PTR [-88+rbp]                      #58.33[spill]
        adcx      r13, r10                                      #57.32
        mov       rdx, QWORD PTR [72+r14]                       #58.33
        setb      cl                                            #57.32
        mov       QWORD PTR [-304+rbp], r13                     #57.32[spill]
        mov       QWORD PTR [-296+rbp], rcx                     #70.34[spill]
        mulx      r11, r13, QWORD PTR [64+r14]                  #58.33
        mulx      rcx, r12, QWORD PTR [72+r14]                  #59.33
        mulx      rax, r10, QWORD PTR [80+r14]                  #60.33
        mulx      rdx, r9, QWORD PTR [88+r14]                   #61.33
        mov       r14d, esi                                     #62.32
        adox      r14d, esi                                     #62.32
        adox      r13, rcx                                      #62.32
        mov       ecx, esi                                      #64.32
        adox      r12, rax                                      #63.32
        adox      r10, rdx                                      #64.32
        seto      cl                                            #64.32
        clc                                                     #65.30
        adcx      rcx, r9                                       #65.30
        mov       r9d, esi                                      #66.34
        adox      r9d, esi                                      #66.34
        mov       rax, 0x0ffffffff                              #72.35
        mov       r9, QWORD PTR [-304+rbp]                      #69.34[spill]
        adox      r15, r11                                      #66.34
        mov       rdx, r15                                      #71.35
        adox      rdi, r13                                      #67.34
        mov       r13, QWORD PTR [-296+rbp]                     #70.34[spill]
        adox      r8, r12                                       #68.34
        mov       r12d, esi                                     #70.34
        adox      r9, r10                                       #69.34
        mulx      r10, r14, rax                                 #72.35
        mov       eax, 0                                        #75.34
        adox      r13, rcx                                      #70.34
        mov       rcx, -1                                       #71.35
        seto      r12b                                          #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-288+rbp], r12d                    #70.34[spill]
        mulx      r12, r11, rcx                                 #71.35
        mov       rcx, 0xffffffff00000001                       #73.35
        adcx      r11, r10                                      #74.34
        mulx      r10, rcx, rcx                                 #73.35
        mov       edx, esi                                      #77.31
        adcx      r14, rax                                      #75.34
        adcx      r10, rax                                      #76.34
        mov       eax, esi                                      #76.34
        setb      al                                            #76.34
        adox      edx, esi                                      #77.31
        adox      rax, rcx                                      #77.31
        clc                                                     #78.31
        mov       rcx, QWORD PTR [-88+rbp]                      #84.35[spill]
        adcx      r15, r12                                      #78.31
        mov       r15d, esi                                     #82.34
        adcx      rdi, r11                                      #79.34
        mov       rdx, QWORD PTR [80+rcx]                       #84.35
        adcx      r8, r14                                       #80.34
        mulx      r11, r14, QWORD PTR [72+rcx]                  #85.35
        adcx      r9, r10                                       #81.34
        mulx      r12, r10, QWORD PTR [64+rcx]                  #84.35
        adcx      r13, rax                                      #82.34
        mov       QWORD PTR [-296+rbp], r13                     #82.34[spill]
        setb      r15b                                          #82.34
        mov       DWORD PTR [-280+rbp], r15d                    #82.34[spill]
        mov       r15d, esi                                     #88.34
        adox      r15d, esi                                     #88.34
        mulx      r13, rax, QWORD PTR [80+rcx]                  #86.35
        mov       r15d, esi                                     #90.34
        adox      r10, r11                                      #88.34
        mov       r11d, esi                                     #95.34
        mulx      rdx, rcx, QWORD PTR [88+rcx]                  #87.35
        adox      r14, r13                                      #89.34
        adox      rax, rdx                                      #90.34
        seto      r15b                                          #90.34
        clc                                                     #91.31
        adcx      r15, rcx                                      #91.31
        mov       ecx, esi                                      #92.34
        adox      ecx, esi                                      #92.34
        mov       rcx, QWORD PTR [-296+rbp]                     #95.34[spill]
        adox      rdi, r12                                      #92.34
        mov       rdx, rdi                                      #97.35
        adox      r8, r10                                       #93.34
        adox      r9, r14                                       #94.34
        mov       r14, 0x0ffffffff                              #98.35
        adox      rcx, rax                                      #95.34
        mov       eax, DWORD PTR [-288+rbp]                     #96.34[spill]
        seto      r11b                                          #95.34
        xor       r12d, r12d                                    #95.34
        mov       r10, -1                                       #95.34
        add       eax, DWORD PTR [-280+rbp]                     #96.34[spill]
        cmp       esi, r11d                                     #96.34
        adcx      rax, r15                                      #96.34
        mulx      r15, r13, r10                                 #97.35
        mov       r10, 0xffffffff00000001                       #99.35
        setb      r12b                                          #96.34
        mov       DWORD PTR [-272+rbp], r12d                    #96.34[spill]
        mulx      r12, r11, r14                                 #98.35
        mulx      r14, r10, r10                                 #99.35
        mov       edx, esi                                      #100.34
        adox      edx, esi                                      #100.34
        adox      r13, r12                                      #100.34
        mov       r12d, 0                                       #101.34
        adox      r11, r12                                      #101.34
        adox      r14, r12                                      #102.34
        mov       r12d, esi                                     #102.34
        seto      r12b                                          #102.34
        clc                                                     #103.31
        adcx      r12, r10                                      #103.31
        mov       r10d, esi                                     #104.31
        adox      r10d, esi                                     #104.31
        adox      rdi, r15                                      #104.31
        mov       edi, esi                                      #108.34
        adox      r8, r13                                       #105.34
        adox      r9, r11                                       #106.34
        mov       r11, QWORD PTR [-88+rbp]                      #110.35[spill]
        adox      rcx, r14                                      #107.34
        mov       rdx, QWORD PTR [88+r11]                       #110.35
        adox      rax, r12                                      #108.34
        mulx      r12, r14, QWORD PTR [64+r11]                  #110.35
        seto      dil                                           #108.34
        clc                                                     #114.34
        mulx      r13, r15, QWORD PTR [72+r11]                  #111.35
        adcx      r14, r13                                      #114.34
        mulx      r13, r10, QWORD PTR [80+r11]                  #112.35
        adcx      r15, r13                                      #115.34
        mulx      r13, r11, QWORD PTR [88+r11]                  #113.35
        mov       edx, esi                                      #117.31
        adcx      r10, r13                                      #116.34
        mov       r13d, esi                                     #116.34
        setb      r13b                                          #116.34
        adox      edx, esi                                      #117.31
        adox      r13, r11                                      #117.31
        clc                                                     #118.34
        mov       r11d, DWORD PTR [-272+rbp]                    #122.34[spill]
        adcx      r8, r12                                       #118.34
        mov       rdx, r8                                       #123.35
        adcx      r9, r14                                       #119.34
        adcx      rcx, r15                                      #120.34
        mov       r15d, esi                                     #121.34
        adcx      rax, r10                                      #121.34
        mov       r10, 0x0ffffffff                              #124.35
        setb      r15b                                          #121.34
        add       r11d, edi                                     #122.34
        xor       edi, edi                                      #122.34
        cmp       esi, r15d                                     #122.34
        adcx      r11, r13                                      #122.34
        mov       r13, -1                                       #123.35
        mulx      r12, r14, r13                                 #123.35
        setb      dil                                           #122.34
        mov       DWORD PTR [-264+rbp], edi                     #122.34[spill]
        mov       rdi, 0xffffffff00000001                       #125.35
        mulx      r10, r13, r10                                 #124.35
        mulx      rdi, r15, rdi                                 #125.35
        mov       edx, esi                                      #126.34
        adox      edx, esi                                      #126.34
        mov       edx, esi                                      #128.34
        adox      r14, r10                                      #126.34
        mov       r10d, 0                                       #127.34
        adox      r13, r10                                      #127.34
        adox      rdi, r10                                      #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r15                                      #129.31
        mov       r15d, esi                                     #130.31
        adox      r15d, esi                                     #130.31
        adox      r8, r12                                       #130.31
        mov       r8d, esi                                      #134.34
        adox      r9, r14                                       #131.34
        mov       r14d, DWORD PTR [-264+rbp]                    #140.31[spill]
        adox      rcx, r13                                      #132.34
        mov       r13, r9                                       #136.34
        adox      rax, rdi                                      #133.34
        mov       rdi, 0xffffffff00000001                       #139.34
        adox      r11, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r8b                                           #134.34
        xor       r15d, r15d                                    #134.34
        mov       r12, -1                                       #134.34
        add       r14d, r8d                                     #140.31
        sub       r13, r12                                      #136.34
        mov       r12, rcx                                      #137.34
        mov       r8, rax                                       #138.34
        sbb       r12, rdx                                      #137.34
        mov       rdx, r11                                      #139.34
        sbb       r8, r10                                       #138.34
        sbb       rdx, rdi                                      #139.34
        setb      r15b                                          #139.34
        cmp       esi, r15d                                     #140.31
        sbb       r14, r10                                      #140.31
        setb      sil                                           #140.31
        testq rsi, rsi;
        cmovnzq r11, rdx;
        testq rsi, rsi;
        cmovnzq rax, r8;
        testq rsi, rsi;
        cmovnzq rcx, r12;
        testq rsi, rsi;
        cmovnzq r9, r13;
        mov       rax, QWORD PTR [-104+rbp]                     #197.39[spill]
        mov       QWORD PTR [-216+rbp], r13                     #9.0
        mov       QWORD PTR [-240+rbp], rdx                     #196.37
        mov       rcx, QWORD PTR [16+rax]                       #197.39
        or        rcx, QWORD PTR [24+rax]                       #152.23
        or        rcx, QWORD PTR [8+rax]                        #153.23
        or        rcx, QWORD PTR [rax]                          #154.23
        mov       QWORD PTR [-232+rbp], r8                      #196.37
        mov       QWORD PTR [-224+rbp], r12                     #196.37
        mov       QWORD PTR [-112+rbp], rcx                     #154.23[spill]
        vmovups   YMMWORD PTR [-336+rbp], ymm0                  #198.20
        mov       r8, rax                                       #198.66
        xor       r14d, r14d                                    #42.32
        mov       rdx, QWORD PTR [-240+rbp]                     #198.59
        mov       rcx, QWORD PTR [8+r8]                         #198.80
        mov       rsi, QWORD PTR [r8]                           #198.87
        mulx      r12, rdi, rsi                                 #38.33
        mulx      r15, r9, rcx                                  #39.33
        adcx      rdi, r15                                      #42.32
        mov       r15, 0x0ffffffff                              #47.33
        mov       rax, QWORD PTR [16+r8]                        #198.73
        mov       r11, QWORD PTR [24+r8]                        #198.66
        mulx      r8, r10, rax                                  #40.33
        adcx      r9, r8                                        #43.32
        mov       r8d, 0                                        #44.32
        mov       QWORD PTR [-192+rbp], rcx                     #198.80[spill]
        mulx      r13, rcx, r11                                 #41.33
        mov       rdx, r12                                      #46.33
        adcx      r10, r13                                      #44.32
        mov       QWORD PTR [-80+rbp], rsi                      #198.87[spill]
        mov       esi, r8d                                      #45.30
        setb      r14b                                          #44.32
        adox      esi, r8d                                      #45.30
        adox      r14, rcx                                      #45.30
        mov       ecx, 0                                        #50.32
        mov       QWORD PTR [-200+rbp], rax                     #198.73[spill]
        mov       eax, r8d                                      #45.30
        mov       QWORD PTR [-208+rbp], r11                     #198.66[spill]
        mov       r11, -1                                       #46.33
        seto      al                                            #45.30
        clc                                                     #49.32
        mulx      r13, r11, r11                                 #46.33
        mulx      rsi, r15, r15                                 #47.33
        adcx      r11, rsi                                      #49.32
        mov       rsi, 0xffffffff00000001                       #48.33
        mulx      rax, rsi, rsi                                 #48.33
        mov       edx, r8d                                      #52.30
        adcx      r15, rcx                                      #50.32
        adcx      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        setb      cl                                            #51.32
        adox      edx, r8d                                      #52.30
        adox      rcx, rsi                                      #52.30
        mov       rdx, QWORD PTR [-232+rbp]                     #58.33
        clc                                                     #53.30
        adcx      r12, r13                                      #53.30
        mov       r13d, r8d                                     #62.32
        mov       r12d, r8d                                     #57.32
        adcx      rdi, r11                                      #54.32
        adcx      r9, r15                                       #55.32
        adcx      r10, rax                                      #56.32
        adcx      r14, rcx                                      #57.32
        mov       QWORD PTR [-304+rbp], r14                     #57.32[spill]
        setb      r12b                                          #57.32
        adox      r13d, r8d                                     #62.32
        mov       r13, 0x0ffffffff                              #72.35
        mov       QWORD PTR [-296+rbp], r12                     #70.34[spill]
        mulx      r14, r15, QWORD PTR [-80+rbp]                 #58.33[spill]
        mulx      rax, r12, QWORD PTR [-192+rbp]                #59.33[spill]
        adox      r15, rax                                      #62.32
        mov       eax, r8d                                      #64.32
        mulx      r11, rcx, QWORD PTR [-200+rbp]                #60.33[spill]
        adox      r12, r11                                      #63.32
        mulx      rdx, rsi, QWORD PTR [-208+rbp]                #61.33[spill]
        adox      rcx, rdx                                      #64.32
        seto      al                                            #64.32
        clc                                                     #65.30
        adcx      rax, rsi                                      #65.30
        mov       esi, r8d                                      #66.34
        adox      esi, r8d                                      #66.34
        mov       rsi, QWORD PTR [-304+rbp]                     #69.34[spill]
        adox      rdi, r14                                      #66.34
        mov       r14, QWORD PTR [-296+rbp]                     #70.34[spill]
        mov       rdx, rdi                                      #71.35
        adox      r9, r15                                       #67.34
        mov       r15, -1                                       #71.35
        adox      r10, r12                                      #68.34
        adox      rsi, rcx                                      #69.34
        mov       ecx, r8d                                      #70.34
        adox      r14, rax                                      #70.34
        mulx      r12, rax, r15                                 #71.35
        mov       r15, 0xffffffff00000001                       #73.35
        seto      cl                                            #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-288+rbp], ecx                     #70.34[spill]
        mulx      rcx, r11, r13                                 #72.35
        mov       r13d, 0                                       #75.34
        adcx      rax, rcx                                      #74.34
        mulx      r15, rcx, r15                                 #73.35
        mov       edx, r8d                                      #77.31
        adcx      r11, r13                                      #75.34
        adcx      r15, r13                                      #76.34
        mov       r13d, r8d                                     #76.34
        setb      r13b                                          #76.34
        adox      edx, r8d                                      #77.31
        adox      r13, rcx                                      #77.31
        mov       rdx, QWORD PTR [-224+rbp]                     #84.35
        clc                                                     #78.31
        adcx      rdi, r12                                      #78.31
        mov       edi, r8d                                      #82.34
        adcx      r9, rax                                       #79.34
        mulx      rax, r12, QWORD PTR [-192+rbp]                #85.35[spill]
        adcx      r10, r11                                      #80.34
        adcx      rsi, r15                                      #81.34
        adcx      r14, r13                                      #82.34
        mov       r13d, r8d                                     #88.34
        mov       QWORD PTR [-296+rbp], r14                     #82.34[spill]
        setb      dil                                           #82.34
        adox      r13d, r8d                                     #88.34
        mulx      r14, r15, QWORD PTR [-80+rbp]                 #84.35[spill]
        adox      r15, rax                                      #88.34
        mov       DWORD PTR [-280+rbp], edi                     #82.34[spill]
        mulx      r11, rdi, QWORD PTR [-200+rbp]                #86.35[spill]
        adox      r12, r11                                      #89.34
        mov       r11d, r8d                                     #90.34
        mulx      rdx, rcx, QWORD PTR [-208+rbp]                #87.35[spill]
        adox      rdi, rdx                                      #90.34
        seto      r11b                                          #90.34
        clc                                                     #91.31
        adcx      r11, rcx                                      #91.31
        mov       ecx, r8d                                      #92.34
        adox      ecx, r8d                                      #92.34
        mov       rcx, QWORD PTR [-296+rbp]                     #95.34[spill]
        adox      r9, r14                                       #92.34
        mov       r14d, r8d                                     #95.34
        mov       eax, DWORD PTR [-288+rbp]                     #96.34[spill]
        mov       rdx, r9                                       #97.35
        adox      r10, r15                                      #93.34
        adox      rsi, r12                                      #94.34
        adox      rcx, rdi                                      #95.34
        mov       rdi, 0x0ffffffff                              #98.35
        seto      r14b                                          #95.34
        xor       r15d, r15d                                    #95.34
        mov       r12, -1                                       #95.34
        add       eax, DWORD PTR [-280+rbp]                     #96.34[spill]
        cmp       r8d, r14d                                     #96.34
        mov       r14, 0xffffffff00000001                       #99.35
        adcx      rax, r11                                      #96.34
        mulx      r11, rdi, rdi                                 #98.35
        setb      r15b                                          #96.34
        mov       DWORD PTR [-184+rbp], r15d                    #96.34[spill]
        mulx      r15, r13, r12                                 #97.35
        mulx      r14, r12, r14                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-216+rbp]                     #110.35
        adox      r13, r11                                      #100.34
        mov       r11d, 0                                       #101.34
        adox      rdi, r11                                      #101.34
        adox      r14, r11                                      #102.34
        mov       r11d, r8d                                     #102.34
        seto      r11b                                          #102.34
        clc                                                     #103.31
        adcx      r11, r12                                      #103.31
        mov       r12d, r8d                                     #104.31
        adox      r12d, r8d                                     #104.31
        mov       r12d, r8d                                     #108.34
        adox      r9, r15                                       #104.31
        adox      r10, r13                                      #105.34
        adox      rsi, rdi                                      #106.34
        mulx      r9, rdi, QWORD PTR [-192+rbp]                 #111.35[spill]
        adox      rcx, r14                                      #107.34
        mulx      r14, r15, QWORD PTR [-80+rbp]                 #110.35[spill]
        adox      rax, r11                                      #108.34
        mulx      r11, r13, QWORD PTR [-200+rbp]                #112.35[spill]
        seto      r12b                                          #108.34
        clc                                                     #114.34
        adcx      r15, r9                                       #114.34
        adcx      rdi, r11                                      #115.34
        mulx      r9, r11, QWORD PTR [-208+rbp]                 #113.35[spill]
        mov       edx, r8d                                      #117.31
        adcx      r13, r9                                       #116.34
        mov       r9d, r8d                                      #116.34
        setb      r9b                                           #116.34
        adox      edx, r8d                                      #117.31
        adox      r9, r11                                       #117.31
        clc                                                     #118.34
        mov       r11d, DWORD PTR [-184+rbp]                    #122.34[spill]
        adcx      r10, r14                                      #118.34
        mov       rdx, r10                                      #123.35
        adcx      rsi, r15                                      #119.34
        mov       r15, -1                                       #123.35
        adcx      rcx, rdi                                      #120.34
        mulx      r15, rdi, r15                                 #123.35
        adcx      rax, r13                                      #121.34
        mov       r13d, r8d                                     #121.34
        setb      r13b                                          #121.34
        xor       r14d, r14d                                    #121.34
        add       r11d, r12d                                    #122.34
        cmp       r8d, r13d                                     #122.34
        mov       r12, 0x0ffffffff                              #124.35
        adcx      r11, r9                                       #122.34
        mov       r9, 0xffffffff00000001                        #125.35
        mulx      r9, r13, r9                                   #125.35
        setb      r14b                                          #122.34
        mov       DWORD PTR [-176+rbp], r14d                    #122.34[spill]
        mulx      r12, r14, r12                                 #124.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      rdi, r12                                      #126.34
        mov       r12d, 0                                       #127.34
        adox      r14, r12                                      #127.34
        adox      r9, r12                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r15                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      rsi, rdi                                      #131.34
        mov       edi, DWORD PTR [-176+rbp]                     #140.31[spill]
        adox      rcx, r14                                      #132.34
        mov       r14, rsi                                      #136.34
        adox      rax, r9                                       #133.34
        mov       r9, 0xffffffff00000001                        #139.34
        adox      r11, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       r15, -1                                       #134.34
        add       edi, r10d                                     #140.31
        sub       r14, r15                                      #136.34
        mov       r15, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       r15, rdx                                      #137.34
        mov       rdx, r11                                      #139.34
        sbb       r10, r12                                      #138.34
        sbb       rdx, r9                                       #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       rdi, r12                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq r11, rdx;
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, r15;
        testq r8, r8;
        cmovnzq rsi, r14;
        mov       QWORD PTR [-216+rbp], r14                     #9.0
        mov       QWORD PTR [-240+rbp], rdx                     #198.34
        mov       QWORD PTR [-232+rbp], r10                     #198.34
        mov       QWORD PTR [-224+rbp], r15                     #198.34
        vmovups   YMMWORD PTR [-272+rbp], ymm0                  #200.21
        mov       r8, QWORD PTR [-88+rbp]                       #38.33[spill]
        mov       rdx, QWORD PTR [-240+rbp]                     #200.61
        xor       r14d, r14d                                    #42.32
        xor       r13d, r13d                                    #42.32
        xor       esi, esi                                      #42.32
        mulx      r12, rdi, QWORD PTR [64+r8]                   #38.33
        mulx      rcx, r9, QWORD PTR [72+r8]                    #39.33
        adcx      rdi, rcx                                      #42.32
        mov       rcx, -1                                       #46.33
        mulx      rax, r10, QWORD PTR [80+r8]                   #40.33
        adcx      r9, rax                                       #43.32
        mov       rax, 0x0ffffffff                              #47.33
        mulx      r15, r11, QWORD PTR [88+r8]                   #41.33
        mov       r8d, 0                                        #44.32
        adcx      r10, r15                                      #44.32
        setb      r14b                                          #44.32
        mov       rdx, r12                                      #46.33
        adox      r13d, r8d                                     #45.30
        adox      r14, r11                                      #45.30
        mulx      r13, r11, rcx                                 #46.33
        mov       ecx, 0                                        #50.32
        seto      sil                                           #45.30
        clc                                                     #49.32
        mulx      rsi, r15, rax                                 #47.33
        adcx      r11, rsi                                      #49.32
        mov       rsi, 0xffffffff00000001                       #48.33
        mulx      rax, rsi, rsi                                 #48.33
        mov       edx, r8d                                      #52.30
        adcx      r15, rcx                                      #50.32
        adcx      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        setb      cl                                            #51.32
        adox      edx, r8d                                      #52.30
        adox      rcx, rsi                                      #52.30
        mov       rdx, QWORD PTR [-232+rbp]                     #58.33
        clc                                                     #53.30
        adcx      r12, r13                                      #53.30
        mov       r13, QWORD PTR [-88+rbp]                      #58.33[spill]
        adcx      rdi, r11                                      #54.32
        adcx      r9, r15                                       #55.32
        mov       r15d, r8d                                     #57.32
        adcx      r10, rax                                      #56.32
        mulx      rax, r11, QWORD PTR [72+r13]                  #59.33
        adcx      r14, rcx                                      #57.32
        mov       QWORD PTR [-184+rbp], r14                     #57.32[spill]
        setb      r15b                                          #57.32
        mov       QWORD PTR [-176+rbp], r15                     #70.34[spill]
        mulx      r12, r14, QWORD PTR [64+r13]                  #58.33
        mulx      r15, rcx, QWORD PTR [80+r13]                  #60.33
        mulx      rdx, rsi, QWORD PTR [88+r13]                  #61.33
        mov       r13d, r8d                                     #62.32
        adox      r13d, r8d                                     #62.32
        mov       r13d, 0                                       #75.34
        adox      r14, rax                                      #62.32
        mov       eax, r8d                                      #64.32
        adox      r11, r15                                      #63.32
        mov       r15d, r8d                                     #66.34
        adox      rcx, rdx                                      #64.32
        seto      al                                            #64.32
        clc                                                     #65.30
        adcx      rax, rsi                                      #65.30
        adox      r15d, r8d                                     #66.34
        mov       rsi, QWORD PTR [-184+rbp]                     #69.34[spill]
        mov       r15, 0xffffffff00000001                       #73.35
        adox      rdi, r12                                      #66.34
        mov       r12d, r8d                                     #70.34
        mov       rdx, rdi                                      #71.35
        adox      r9, r14                                       #67.34
        mov       r14, QWORD PTR [-176+rbp]                     #70.34[spill]
        adox      r10, r11                                      #68.34
        mov       r11, 0x0ffffffff                              #72.35
        adox      rsi, rcx                                      #69.34
        mov       rcx, -1                                       #71.35
        adox      r14, rax                                      #70.34
        seto      r12b                                          #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-168+rbp], r12d                    #70.34[spill]
        mulx      r12, rax, rcx                                 #71.35
        mulx      rcx, r11, r11                                 #72.35
        adcx      rax, rcx                                      #74.34
        mulx      r15, rcx, r15                                 #73.35
        mov       edx, r8d                                      #77.31
        adcx      r11, r13                                      #75.34
        adcx      r15, r13                                      #76.34
        mov       r13d, r8d                                     #76.34
        setb      r13b                                          #76.34
        adox      edx, r8d                                      #77.31
        adox      r13, rcx                                      #77.31
        mov       rdx, QWORD PTR [-224+rbp]                     #84.35
        clc                                                     #78.31
        adcx      rdi, r12                                      #78.31
        mov       edi, r8d                                      #82.34
        adcx      r9, rax                                       #79.34
        adcx      r10, r11                                      #80.34
        adcx      rsi, r15                                      #81.34
        adcx      r14, r13                                      #82.34
        mov       r13, QWORD PTR [-88+rbp]                      #84.35[spill]
        setb      dil                                           #82.34
        mov       QWORD PTR [-176+rbp], r14                     #82.34[spill]
        mov       DWORD PTR [-160+rbp], edi                     #82.34[spill]
        mulx      r12, r14, QWORD PTR [64+r13]                  #84.35
        mulx      rax, r11, QWORD PTR [72+r13]                  #85.35
        mulx      r15, rdi, QWORD PTR [80+r13]                  #86.35
        mulx      rdx, rcx, QWORD PTR [88+r13]                  #87.35
        mov       r13d, r8d                                     #88.34
        adox      r13d, r8d                                     #88.34
        mov       r13d, r8d                                     #90.34
        adox      r14, rax                                      #88.34
        adox      r11, r15                                      #89.34
        mov       r15d, r8d                                     #95.34
        adox      rdi, rdx                                      #90.34
        seto      r13b                                          #90.34
        clc                                                     #91.31
        adcx      r13, rcx                                      #91.31
        mov       ecx, r8d                                      #92.34
        adox      ecx, r8d                                      #92.34
        mov       rcx, QWORD PTR [-176+rbp]                     #95.34[spill]
        adox      r9, r12                                       #92.34
        mov       eax, DWORD PTR [-168+rbp]                     #96.34[spill]
        mov       rdx, r9                                       #97.35
        adox      r10, r14                                      #93.34
        mov       r14, 0x0ffffffff                              #98.35
        adox      rsi, r11                                      #94.34
        adox      rcx, rdi                                      #95.34
        seto      r15b                                          #95.34
        xor       r12d, r12d                                    #95.34
        mov       rdi, -1                                       #95.34
        add       eax, DWORD PTR [-160+rbp]                     #96.34[spill]
        cmp       r8d, r15d                                     #96.34
        adcx      rax, r13                                      #96.34
        mulx      r15, r13, rdi                                 #97.35
        setb      r12b                                          #96.34
        mov       DWORD PTR [-152+rbp], r12d                    #96.34[spill]
        mov       r12, 0xffffffff00000001                       #99.35
        mulx      r14, rdi, r14                                 #98.35
        mulx      r11, r12, r12                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-216+rbp]                     #110.35
        adox      r13, r14                                      #100.34
        mov       r14d, 0                                       #101.34
        adox      rdi, r14                                      #101.34
        adox      r11, r14                                      #102.34
        mov       r14d, r8d                                     #102.34
        seto      r14b                                          #102.34
        clc                                                     #103.31
        adcx      r14, r12                                      #103.31
        mov       r12d, r8d                                     #104.31
        adox      r12d, r8d                                     #104.31
        mov       r12, QWORD PTR [-88+rbp]                      #110.35[spill]
        adox      r9, r15                                       #104.31
        mov       r9d, r8d                                      #108.34
        adox      r10, r13                                      #105.34
        mulx      r13, r15, QWORD PTR [64+r12]                  #110.35
        adox      rsi, rdi                                      #106.34
        adox      rcx, r11                                      #107.34
        adox      rax, r14                                      #108.34
        mulx      r11, r14, QWORD PTR [72+r12]                  #111.35
        seto      r9b                                           #108.34
        clc                                                     #114.34
        adcx      r15, r11                                      #114.34
        mulx      r11, rdi, QWORD PTR [80+r12]                  #112.35
        adcx      r14, r11                                      #115.34
        mulx      r12, r11, QWORD PTR [88+r12]                  #113.35
        mov       edx, r8d                                      #117.31
        adcx      rdi, r12                                      #116.34
        mov       r12d, r8d                                     #116.34
        setb      r12b                                          #116.34
        adox      edx, r8d                                      #117.31
        adox      r12, r11                                      #117.31
        clc                                                     #118.34
        adcx      r10, r13                                      #118.34
        mov       rdx, r10                                      #123.35
        adcx      rsi, r15                                      #119.34
        mov       r15d, r8d                                     #121.34
        adcx      rcx, r14                                      #120.34
        mov       r14, 0x0ffffffff                              #124.35
        adcx      rax, rdi                                      #121.34
        mov       edi, DWORD PTR [-152+rbp]                     #122.34[spill]
        setb      r15b                                          #121.34
        add       edi, r9d                                      #122.34
        xor       r9d, r9d                                      #122.34
        cmp       r8d, r15d                                     #122.34
        mov       r15, -1                                       #123.35
        adcx      rdi, r12                                      #122.34
        mulx      r12, r11, r15                                 #123.35
        setb      r9b                                           #122.34
        mov       DWORD PTR [-144+rbp], r9d                     #122.34[spill]
        mov       r9, 0xffffffff00000001                        #125.35
        mulx      r14, r15, r14                                 #124.35
        mulx      r9, r13, r9                                   #125.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      r11, r14                                      #126.34
        mov       r14d, 0                                       #127.34
        adox      r15, r14                                      #127.34
        adox      r9, r14                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r12                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      rsi, r11                                      #131.34
        mov       r11d, DWORD PTR [-144+rbp]                    #140.31[spill]
        adox      rcx, r15                                      #132.34
        mov       r15, rsi                                      #136.34
        adox      rax, r9                                       #133.34
        mov       r9, 0xffffffff00000001                        #139.34
        adox      rdi, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       r12, -1                                       #134.34
        add       r11d, r10d                                    #140.31
        sub       r15, r12                                      #136.34
        mov       r12, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       r12, rdx                                      #137.34
        mov       rdx, rdi                                      #139.34
        sbb       r10, r14                                      #138.34
        sbb       rdx, r9                                       #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       r11, r14                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq rdi, rdx;
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, r12;
        testq r8, r8;
        cmovnzq rsi, r15;
        mov       QWORD PTR [-248+rbp], r15                     #9.0
        mov       QWORD PTR [-272+rbp], rdx                     #200.35
        mov       QWORD PTR [-264+rbp], r10                     #200.35
        mov       QWORD PTR [-256+rbp], r12                     #200.35
        vmovups   YMMWORD PTR [-304+rbp], ymm0                  #201.19
        mov       r15, QWORD PTR [-88+rbp]                      #159.32[spill]
        xor       r11d, r11d                                    #9.0
        mov       r12, QWORD PTR [-200+rbp]                     #152.23[spill]
        xor       edi, edi                                      #168.32
        or        r12, QWORD PTR [-208+rbp]                     #152.23[spill]
        mov       rsi, QWORD PTR [-336+rbp]                     #159.32
        mov       r9, QWORD PTR [-192+rbp]                      #153.23[spill]
        or        r9, r12                                       #153.23
        xor       r12d, r12d                                    #162.32
        xor       r10d, r10d                                    #159.32
        sub       rsi, QWORD PTR [r15]                          #159.32
        mov       r14, QWORD PTR [-328+rbp]                     #160.32
        sbb       r14, QWORD PTR [8+r15]                        #160.32
        mov       rcx, QWORD PTR [-320+rbp]                     #161.32
        sbb       rcx, QWORD PTR [16+r15]                       #161.32
        mov       r13, QWORD PTR [-312+rbp]                     #162.32
        sbb       r13, QWORD PTR [24+r15]                       #162.32
        setb      r10b                                          #162.32
        xor       r8d, r8d                                      #162.32
        or        QWORD PTR [-80+rbp], r9                       #154.23[spill]
        mov       r9, -1                                        #9.0
        testq r10, r10;
        cmovnzq r9, r11;
        xor       edx, edx                                      #165.32
        mov       eax, r11d                                     #167.32
        mov       r9, 0xffffffff00000001                        #170.30
        adcx      rsi, r11                                      #165.32
        mov       rdx, QWORD PTR [64+r15]                       #38.33
        adcx      r14, rax                                      #167.32
        mov       QWORD PTR [-184+rbp], rsi                     #165.32[spill]
        adcx      rcx, rdi                                      #168.32
        mov       QWORD PTR [-168+rbp], rcx                     #168.32[spill]
        setb      r8b                                           #168.32
        xor       r15d, r15d                                    #168.32
        and       r11, r9                                       #170.30
        cmp       r12d, r8d                                     #170.30
        mov       QWORD PTR [-296+rbp], rcx                     #201.33
        adcx      r13, r11                                      #170.30
        mov       QWORD PTR [-160+rbp], r13                     #170.30[spill]
        adox      r15d, r12d                                    #42.32
        mov       QWORD PTR [-304+rbp], r13                     #201.33
        mov       r15d, r12d                                    #44.32
        mulx      r8, r10, r13                                  #38.33
        mulx      rcx, r13, rcx                                 #39.33
        adox      r10, rcx                                      #42.32
        mov       rcx, -1                                       #46.33
        mulx      rax, r11, r14                                 #40.33
        adox      r13, rax                                      #43.32
        mov       QWORD PTR [-280+rbp], rsi                     #201.33
        mov       QWORD PTR [-176+rbp], r14                     #167.32[spill]
        mov       QWORD PTR [-288+rbp], r14                     #201.33
        mulx      r14, rsi, rsi                                 #41.33
        mov       rdx, r8                                       #46.33
        adox      r11, r14                                      #44.32
        seto      r15b                                          #44.32
        clc                                                     #45.30
        adcx      r15, rsi                                      #45.30
        mov       QWORD PTR [-152+rbp], r15                     #45.30[spill]
        mulx      r15, r14, rcx                                 #46.33
        mov       ecx, r12d                                     #49.32
        adox      ecx, r12d                                     #49.32
        mov       rsi, 0x0ffffffff                              #47.33
        mulx      rax, rsi, rsi                                 #47.33
        mov       ecx, r12d                                     #51.32
        adox      r14, rax                                      #49.32
        mov       eax, r12d                                     #53.30
        mulx      r9, rdx, r9                                   #48.33
        adox      rsi, rdi                                      #50.32
        adox      r9, rdi                                       #51.32
        seto      cl                                            #51.32
        clc                                                     #52.30
        adcx      rcx, rdx                                      #52.30
        adox      eax, r12d                                     #53.30
        adox      r8, r15                                       #53.30
        mov       r15, QWORD PTR [-88+rbp]                      #58.33[spill]
        adox      r10, r14                                      #54.32
        mov       rdx, QWORD PTR [72+r15]                       #58.33
        adox      r13, rsi                                      #55.32
        mov       rsi, QWORD PTR [-152+rbp]                     #57.32[spill]
        adox      r11, r9                                       #56.32
        mulx      r8, rdi, QWORD PTR [-160+rbp]                 #58.33[spill]
        adox      rsi, rcx                                      #57.32
        mov       ecx, r12d                                     #57.32
        mulx      r9, rax, QWORD PTR [-168+rbp]                 #59.33[spill]
        seto      cl                                            #57.32
        clc                                                     #62.32
        adcx      rdi, r9                                       #62.32
        mulx      r14, r9, QWORD PTR [-176+rbp]                 #60.33[spill]
        adcx      rax, r14                                      #63.32
        mulx      r15, r14, QWORD PTR [-184+rbp]                #61.33[spill]
        mov       edx, r12d                                     #65.30
        adcx      r9, r15                                       #64.32
        mov       r15d, r12d                                    #64.32
        setb      r15b                                          #64.32
        adox      edx, r12d                                     #65.30
        adox      r15, r14                                      #65.30
        clc                                                     #66.34
        adcx      r10, r8                                       #66.34
        mov       r8d, r12d                                     #70.34
        mov       rdx, r10                                      #71.35
        adcx      r13, rdi                                      #67.34
        mov       rdi, -1                                       #71.35
        adcx      r11, rax                                      #68.34
        adcx      rsi, r9                                       #69.34
        mov       r9, 0x0ffffffff                               #72.35
        adcx      rcx, r15                                      #70.34
        mulx      rax, r15, r9                                  #72.35
        mov       r9, 0xffffffff00000001                        #73.35
        setb      r8b                                           #70.34
        mov       DWORD PTR [-144+rbp], r8d                     #70.34[spill]
        mulx      rdi, r8, rdi                                  #71.35
        mulx      r9, r14, r9                                   #73.35
        mov       edx, r12d                                     #74.34
        adox      edx, r12d                                     #74.34
        adox      r8, rax                                       #74.34
        mov       eax, 0                                        #75.34
        adox      r15, rax                                      #75.34
        adox      r9, rax                                       #76.34
        mov       eax, r12d                                     #76.34
        seto      al                                            #76.34
        clc                                                     #77.31
        adcx      rax, r14                                      #77.31
        mov       r14d, r12d                                    #78.31
        adox      r14d, r12d                                    #78.31
        mov       r14, QWORD PTR [-88+rbp]                      #84.35[spill]
        adox      r10, rdi                                      #78.31
        mov       r10d, r12d                                    #82.34
        adox      r13, r8                                       #79.34
        mov       rdx, QWORD PTR [80+r14]                       #84.35
        adox      r11, r15                                      #80.34
        mulx      rdi, r15, QWORD PTR [-168+rbp]                #85.35[spill]
        adox      rsi, r9                                       #81.34
        adox      rcx, rax                                      #82.34
        mulx      rax, r8, QWORD PTR [-160+rbp]                 #84.35[spill]
        seto      r10b                                          #82.34
        clc                                                     #88.34
        adcx      r8, rdi                                       #88.34
        mulx      r9, rdi, QWORD PTR [-176+rbp]                 #86.35[spill]
        adcx      r15, r9                                       #89.34
        mulx      r14, r9, QWORD PTR [-184+rbp]                 #87.35[spill]
        mov       edx, r12d                                     #91.31
        adcx      rdi, r14                                      #90.34
        mov       r14d, r12d                                    #90.34
        setb      r14b                                          #90.34
        adox      edx, r12d                                     #91.31
        adox      r14, r9                                       #91.31
        clc                                                     #92.34
        adcx      r13, rax                                      #92.34
        mov       eax, DWORD PTR [-144+rbp]                     #96.34[spill]
        mov       rdx, r13                                      #97.35
        adcx      r11, r8                                       #93.34
        mov       r8, 0x0ffffffff                               #98.35
        adcx      rsi, r15                                      #94.34
        mov       r15d, r12d                                    #95.34
        adcx      rcx, rdi                                      #95.34
        setb      r15b                                          #95.34
        mov       r9, -1                                        #95.34
        add       eax, r10d                                     #96.34
        xor       r10d, r10d                                    #96.34
        cmp       r12d, r15d                                    #96.34
        adcx      rax, r14                                      #96.34
        mulx      r15, r14, r8                                  #98.35
        mov       r8, 0xffffffff00000001                        #99.35
        setb      r10b                                          #96.34
        mov       DWORD PTR [-136+rbp], r10d                    #96.34[spill]
        mulx      r10, r9, r9                                   #97.35
        mulx      r8, rdi, r8                                   #99.35
        mov       edx, r12d                                     #100.34
        adox      edx, r12d                                     #100.34
        adox      r9, r15                                       #100.34
        mov       r15d, 0                                       #101.34
        adox      r14, r15                                      #101.34
        adox      r8, r15                                       #102.34
        mov       r15d, r12d                                    #102.34
        seto      r15b                                          #102.34
        clc                                                     #103.31
        adcx      r15, rdi                                      #103.31
        mov       edi, r12d                                     #104.31
        adox      edi, r12d                                     #104.31
        adox      r13, r10                                      #104.31
        mov       r13d, r12d                                    #108.34
        adox      r11, r9                                       #105.34
        adox      rsi, r14                                      #106.34
        adox      rcx, r8                                       #107.34
        adox      rax, r15                                      #108.34
        mov       r15, QWORD PTR [-88+rbp]                      #110.35[spill]
        seto      r13b                                          #108.34
        clc                                                     #114.34
        mov       rdx, QWORD PTR [88+r15]                       #110.35
        mulx      r10, r9, QWORD PTR [-160+rbp]                 #110.35[spill]
        mulx      r14, r8, QWORD PTR [-168+rbp]                 #111.35[spill]
        adcx      r9, r14                                       #114.34
        mulx      rdi, r14, QWORD PTR [-176+rbp]                #112.35[spill]
        adcx      r8, rdi                                       #115.34
        mulx      r15, rdi, QWORD PTR [-184+rbp]                #113.35[spill]
        mov       edx, r12d                                     #117.31
        adcx      r14, r15                                      #116.34
        mov       r15d, r12d                                    #116.34
        setb      r15b                                          #116.34
        adox      edx, r12d                                     #117.31
        adox      r15, rdi                                      #117.31
        clc                                                     #118.34
        adcx      r11, r10                                      #118.34
        mov       rdx, r11                                      #123.35
        adcx      rsi, r9                                       #119.34
        mov       r9d, r12d                                     #121.34
        adcx      rcx, r8                                       #120.34
        mov       r8, 0x0ffffffff                               #124.35
        adcx      rax, r14                                      #121.34
        mov       r14d, DWORD PTR [-136+rbp]                    #122.34[spill]
        setb      r9b                                           #121.34
        add       r14d, r13d                                    #122.34
        xor       r13d, r13d                                    #122.34
        cmp       r12d, r9d                                     #122.34
        mov       r9, -1                                        #123.35
        adcx      r14, r15                                      #122.34
        mulx      r15, rdi, r9                                  #123.35
        setb      r13b                                          #122.34
        mov       DWORD PTR [-128+rbp], r13d                    #122.34[spill]
        mov       r13, 0xffffffff00000001                       #125.35
        mulx      r8, r9, r8                                    #124.35
        mulx      r13, r10, r13                                 #125.35
        mov       edx, r12d                                     #126.34
        adox      edx, r12d                                     #126.34
        mov       edx, r12d                                     #128.34
        adox      rdi, r8                                       #126.34
        mov       r8d, 0                                        #127.34
        adox      r9, r8                                        #127.34
        adox      r13, r8                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r10                                      #129.31
        mov       r10d, r12d                                    #130.31
        adox      r10d, r12d                                    #130.31
        adox      r11, r15                                      #130.31
        mov       r15d, r12d                                    #134.34
        adox      rsi, rdi                                      #131.34
        mov       edi, DWORD PTR [-128+rbp]                     #140.31[spill]
        adox      rcx, r9                                       #132.34
        mov       r9, rsi                                       #136.34
        adox      rax, r13                                      #133.34
        mov       r13, 0xffffffff00000001                       #139.34
        adox      r14, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r15b                                          #134.34
        xor       r10d, r10d                                    #134.34
        mov       r11, -1                                       #134.34
        add       edi, r15d                                     #140.31
        sub       r9, r11                                       #136.34
        mov       r15, rcx                                      #137.34
        mov       r11, r14                                      #139.34
        sbb       r15, rdx                                      #137.34
        mov       rdx, rax                                      #138.34
        sbb       rdx, r8                                       #138.34
        sbb       r11, r13                                      #139.34
        setb      r10b                                          #139.34
        cmp       r12d, r10d                                    #140.31
        sbb       rdi, r8                                       #140.31
        setb      r12b                                          #140.31
        testq r12, r12;
        cmovnzq r14, r11;
        testq r12, r12;
        cmovnzq rax, rdx;
        testq r12, r12;
        cmovnzq rcx, r15;
        testq r12, r12;
        cmovnzq rsi, r9;
        mov       rax, QWORD PTR [-96+rbp]                      #9.0[spill]
        mov       QWORD PTR [72+rax], rdx                       #146.1
        mov       rdx, QWORD PTR [-104+rbp]                     #203.39[spill]
        mov       QWORD PTR [88+rax], r9                        #9.0
        mov       QWORD PTR [64+rax], r11                       #145.1
        mov       QWORD PTR [80+rax], r15                       #147.1
        mov       rcx, QWORD PTR [48+rdx]                       #203.39
        or        rcx, QWORD PTR [56+rdx]                       #152.23
        or        rcx, QWORD PTR [40+rdx]                       #153.23
        or        rcx, QWORD PTR [32+rdx]                       #154.23
        or        QWORD PTR [-80+rbp], rcx                      #204.28[spill]
        vmovups   YMMWORD PTR [-240+rbp], ymm0                  #205.20
        mov       r8, rdx                                       #38.33
        mov       rdx, QWORD PTR [-272+rbp]                     #205.62
        xor       r14d, r14d                                    #42.32
        xor       r13d, r13d                                    #42.32
        xor       esi, esi                                      #42.32
        mulx      r12, rdi, QWORD PTR [32+r8]                   #38.33
        mulx      rcx, r9, QWORD PTR [40+r8]                    #39.33
        adcx      rdi, rcx                                      #42.32
        mov       rcx, -1                                       #46.33
        mulx      rax, r10, QWORD PTR [48+r8]                   #40.33
        adcx      r9, rax                                       #43.32
        mov       rax, 0x0ffffffff                              #47.33
        mulx      r15, r11, QWORD PTR [56+r8]                   #41.33
        mov       r8d, 0                                        #44.32
        adcx      r10, r15                                      #44.32
        setb      r14b                                          #44.32
        mov       rdx, r12                                      #46.33
        adox      r13d, r8d                                     #45.30
        adox      r14, r11                                      #45.30
        mulx      r13, r11, rcx                                 #46.33
        mov       ecx, 0                                        #50.32
        seto      sil                                           #45.30
        clc                                                     #49.32
        mulx      rsi, r15, rax                                 #47.33
        adcx      r11, rsi                                      #49.32
        mov       rsi, 0xffffffff00000001                       #48.33
        mulx      rax, rsi, rsi                                 #48.33
        mov       edx, r8d                                      #52.30
        adcx      r15, rcx                                      #50.32
        adcx      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        setb      cl                                            #51.32
        adox      edx, r8d                                      #52.30
        adox      rcx, rsi                                      #52.30
        mov       rdx, QWORD PTR [-264+rbp]                     #58.33
        clc                                                     #53.30
        adcx      r12, r13                                      #53.30
        mov       r13, QWORD PTR [-104+rbp]                     #58.33[spill]
        adcx      rdi, r11                                      #54.32
        adcx      r9, r15                                       #55.32
        mov       r15d, r8d                                     #57.32
        adcx      r10, rax                                      #56.32
        mulx      rax, r11, QWORD PTR [40+r13]                  #59.33
        adcx      r14, rcx                                      #57.32
        mov       QWORD PTR [-208+rbp], r14                     #57.32[spill]
        setb      r15b                                          #57.32
        mov       QWORD PTR [-200+rbp], r15                     #70.34[spill]
        mulx      r12, r14, QWORD PTR [32+r13]                  #58.33
        mulx      r15, rcx, QWORD PTR [48+r13]                  #60.33
        mulx      rdx, rsi, QWORD PTR [56+r13]                  #61.33
        mov       r13d, r8d                                     #62.32
        adox      r13d, r8d                                     #62.32
        mov       r13d, 0                                       #75.34
        adox      r14, rax                                      #62.32
        mov       eax, r8d                                      #64.32
        adox      r11, r15                                      #63.32
        mov       r15d, r8d                                     #66.34
        adox      rcx, rdx                                      #64.32
        seto      al                                            #64.32
        clc                                                     #65.30
        adcx      rax, rsi                                      #65.30
        adox      r15d, r8d                                     #66.34
        mov       rsi, QWORD PTR [-208+rbp]                     #69.34[spill]
        mov       r15, 0xffffffff00000001                       #73.35
        adox      rdi, r12                                      #66.34
        mov       r12d, r8d                                     #70.34
        mov       rdx, rdi                                      #71.35
        adox      r9, r14                                       #67.34
        mov       r14, QWORD PTR [-200+rbp]                     #70.34[spill]
        adox      r10, r11                                      #68.34
        mov       r11, 0x0ffffffff                              #72.35
        adox      rsi, rcx                                      #69.34
        mov       rcx, -1                                       #71.35
        adox      r14, rax                                      #70.34
        seto      r12b                                          #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-192+rbp], r12d                    #70.34[spill]
        mulx      r12, rax, rcx                                 #71.35
        mulx      rcx, r11, r11                                 #72.35
        adcx      rax, rcx                                      #74.34
        mulx      r15, rcx, r15                                 #73.35
        mov       edx, r8d                                      #77.31
        adcx      r11, r13                                      #75.34
        adcx      r15, r13                                      #76.34
        mov       r13d, r8d                                     #76.34
        setb      r13b                                          #76.34
        adox      edx, r8d                                      #77.31
        adox      r13, rcx                                      #77.31
        mov       rdx, QWORD PTR [-256+rbp]                     #84.35
        clc                                                     #78.31
        adcx      rdi, r12                                      #78.31
        mov       edi, r8d                                      #82.34
        adcx      r9, rax                                       #79.34
        adcx      r10, r11                                      #80.34
        adcx      rsi, r15                                      #81.34
        adcx      r14, r13                                      #82.34
        mov       r13, QWORD PTR [-104+rbp]                     #84.35[spill]
        setb      dil                                           #82.34
        mov       QWORD PTR [-200+rbp], r14                     #82.34[spill]
        mov       DWORD PTR [-184+rbp], edi                     #82.34[spill]
        mulx      r12, r14, QWORD PTR [32+r13]                  #84.35
        mulx      rax, r11, QWORD PTR [40+r13]                  #85.35
        mulx      r15, rdi, QWORD PTR [48+r13]                  #86.35
        mulx      rdx, rcx, QWORD PTR [56+r13]                  #87.35
        mov       r13d, r8d                                     #88.34
        adox      r13d, r8d                                     #88.34
        mov       r13d, r8d                                     #90.34
        adox      r14, rax                                      #88.34
        adox      r11, r15                                      #89.34
        mov       r15d, r8d                                     #95.34
        adox      rdi, rdx                                      #90.34
        seto      r13b                                          #90.34
        clc                                                     #91.31
        adcx      r13, rcx                                      #91.31
        mov       ecx, r8d                                      #92.34
        adox      ecx, r8d                                      #92.34
        mov       rcx, QWORD PTR [-200+rbp]                     #95.34[spill]
        adox      r9, r12                                       #92.34
        mov       eax, DWORD PTR [-192+rbp]                     #96.34[spill]
        mov       rdx, r9                                       #97.35
        adox      r10, r14                                      #93.34
        mov       r14, 0x0ffffffff                              #98.35
        adox      rsi, r11                                      #94.34
        adox      rcx, rdi                                      #95.34
        seto      r15b                                          #95.34
        xor       r12d, r12d                                    #95.34
        mov       rdi, -1                                       #95.34
        add       eax, DWORD PTR [-184+rbp]                     #96.34[spill]
        cmp       r8d, r15d                                     #96.34
        adcx      rax, r13                                      #96.34
        mulx      r15, r13, rdi                                 #97.35
        setb      r12b                                          #96.34
        mov       DWORD PTR [-176+rbp], r12d                    #96.34[spill]
        mov       r12, 0xffffffff00000001                       #99.35
        mulx      r14, rdi, r14                                 #98.35
        mulx      r11, r12, r12                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-248+rbp]                     #110.35
        adox      r13, r14                                      #100.34
        mov       r14d, 0                                       #101.34
        adox      rdi, r14                                      #101.34
        adox      r11, r14                                      #102.34
        mov       r14d, r8d                                     #102.34
        seto      r14b                                          #102.34
        clc                                                     #103.31
        adcx      r14, r12                                      #103.31
        mov       r12d, r8d                                     #104.31
        adox      r12d, r8d                                     #104.31
        mov       r12, QWORD PTR [-104+rbp]                     #110.35[spill]
        adox      r9, r15                                       #104.31
        mov       r9d, r8d                                      #108.34
        adox      r10, r13                                      #105.34
        mulx      r13, r15, QWORD PTR [32+r12]                  #110.35
        adox      rsi, rdi                                      #106.34
        adox      rcx, r11                                      #107.34
        adox      rax, r14                                      #108.34
        mulx      r11, r14, QWORD PTR [40+r12]                  #111.35
        seto      r9b                                           #108.34
        clc                                                     #114.34
        adcx      r15, r11                                      #114.34
        mulx      r11, rdi, QWORD PTR [48+r12]                  #112.35
        adcx      r14, r11                                      #115.34
        mulx      r12, r11, QWORD PTR [56+r12]                  #113.35
        mov       edx, r8d                                      #117.31
        adcx      rdi, r12                                      #116.34
        mov       r12d, r8d                                     #116.34
        setb      r12b                                          #116.34
        adox      edx, r8d                                      #117.31
        adox      r12, r11                                      #117.31
        clc                                                     #118.34
        adcx      r10, r13                                      #118.34
        mov       rdx, r10                                      #123.35
        adcx      rsi, r15                                      #119.34
        mov       r15d, r8d                                     #121.34
        adcx      rcx, r14                                      #120.34
        mov       r14, 0x0ffffffff                              #124.35
        adcx      rax, rdi                                      #121.34
        mov       edi, DWORD PTR [-176+rbp]                     #122.34[spill]
        setb      r15b                                          #121.34
        add       edi, r9d                                      #122.34
        xor       r9d, r9d                                      #122.34
        cmp       r8d, r15d                                     #122.34
        mov       r15, -1                                       #123.35
        adcx      rdi, r12                                      #122.34
        mulx      r12, r11, r15                                 #123.35
        setb      r9b                                           #122.34
        mov       DWORD PTR [-168+rbp], r9d                     #122.34[spill]
        mov       r9, 0xffffffff00000001                        #125.35
        mulx      r14, r15, r14                                 #124.35
        mulx      r9, r13, r9                                   #125.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      r11, r14                                      #126.34
        mov       r14d, 0                                       #127.34
        adox      r15, r14                                      #127.34
        adox      r9, r14                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r12                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      rsi, r11                                      #131.34
        mov       r11d, DWORD PTR [-168+rbp]                    #140.31[spill]
        adox      rcx, r15                                      #132.34
        mov       r15, rsi                                      #136.34
        adox      rax, r9                                       #133.34
        mov       r9, 0xffffffff00000001                        #139.34
        adox      rdi, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       r12, -1                                       #134.34
        add       r11d, r10d                                    #140.31
        sub       r15, r12                                      #136.34
        mov       r12, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       r12, rdx                                      #137.34
        mov       rdx, rdi                                      #139.34
        sbb       r10, r14                                      #138.34
        sbb       rdx, r9                                       #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       r11, r14                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq rdi, rdx;
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, r12;
        testq r8, r8;
        cmovnzq rsi, r15;
        mov       QWORD PTR [-216+rbp], r15                     #9.0
        mov       QWORD PTR [-240+rbp], rdx                     #205.34
        mov       QWORD PTR [-232+rbp], r10                     #205.34
        mov       QWORD PTR [-224+rbp], r12                     #205.34
        vmovups   YMMWORD PTR [-336+rbp], ymm0                  #206.19
        mov       rcx, QWORD PTR [-88+rbp]                      #159.32[spill]
        xor       eax, eax                                      #162.32
        mov       r9, QWORD PTR [-240+rbp]                      #159.32
        xor       esi, esi                                      #162.32
        mov       r11, QWORD PTR [-232+rbp]                     #160.32
        mov       rdi, -1                                       #9.0
        sub       r9, QWORD PTR [32+rcx]                        #159.32
        mov       r13, QWORD PTR [-224+rbp]                     #161.32
        sbb       r11, QWORD PTR [40+rcx]                       #160.32
        mov       r14, 0xffffffff00000001                       #170.30
        mov       rdx, QWORD PTR [-216+rbp]                     #162.32
        sbb       r13, QWORD PTR [48+rcx]                       #161.32
        sbb       rdx, QWORD PTR [56+rcx]                       #162.32
        setb      sil                                           #162.32
        xor       r12d, r12d                                    #162.32
        xor       r15d, r15d                                    #162.32
        xor       ecx, ecx                                      #162.32
        testq rsi, rsi;
        cmovnzq rdi, rcx;
        xor       r8d, r8d                                      #165.32
        mov       r10d, ecx                                     #167.32
        adcx      r9, rcx                                       #165.32
        mov       QWORD PTR [-312+rbp], r9                      #206.33
        adcx      r11, r10                                      #167.32
        mov       QWORD PTR [-320+rbp], r11                     #206.33
        adcx      r13, r12                                      #168.32
        mov       QWORD PTR [-328+rbp], r13                     #206.33
        setb      r15b                                          #168.32
        and       rcx, r14                                      #170.30
        cmp       eax, r15d                                     #170.30
        adcx      rdx, rcx                                      #170.30
        mov       QWORD PTR [-336+rbp], rdx                     #206.33
        vmovups   YMMWORD PTR [-176+rbp], ymm0                  #207.20
        setb      al                                            #170.30
        mov       rdx, QWORD PTR [-304+rbp]                     #207.59
        mov       r13, -1                                       #46.33
        xor       r9d, r9d                                      #42.32
        mov       r15, 0xffffffff00000001                       #48.33
        mulx      r8, rdi, QWORD PTR [-296+rbp]                 #39.33
        mulx      r11, rsi, rdx                                 #38.33
        adox      rsi, r8                                       #42.32
        mov       r8d, 0                                        #44.32
        mulx      rcx, r10, QWORD PTR [-288+rbp]                #40.33
        adox      rdi, rcx                                      #43.32
        mulx      rax, r12, QWORD PTR [-280+rbp]                #41.33
        mov       rdx, r11                                      #46.33
        adox      r10, rax                                      #44.32
        mov       rcx, 0x0ffffffff                              #47.33
        mulx      rax, r15, r15                                 #48.33
        seto      r9b                                           #44.32
        clc                                                     #45.30
        adcx      r9, r12                                       #45.30
        mulx      r13, r12, r13                                 #46.33
        mulx      rcx, r14, rcx                                 #47.33
        mov       edx, r8d                                      #49.32
        adox      edx, r8d                                      #49.32
        mov       rdx, QWORD PTR [-296+rbp]                     #58.33
        adox      r12, rcx                                      #49.32
        mov       ecx, 0                                        #50.32
        adox      r14, rcx                                      #50.32
        adox      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        seto      cl                                            #51.32
        clc                                                     #52.30
        adcx      rcx, r15                                      #52.30
        mov       r15d, r8d                                     #53.30
        adox      r15d, r8d                                     #53.30
        adox      r11, r13                                      #53.30
        mulx      r11, r13, rdx                                 #59.33
        adox      rsi, r12                                      #54.32
        adox      rdi, r14                                      #55.32
        mulx      r12, r14, QWORD PTR [-304+rbp]                #58.33
        adox      r10, rax                                      #56.32
        mulx      rax, r15, QWORD PTR [-288+rbp]                #60.33
        adox      r9, rcx                                       #57.32
        mov       ecx, r8d                                      #57.32
        seto      cl                                            #57.32
        clc                                                     #62.32
        adcx      r14, r11                                      #62.32
        adcx      r13, rax                                      #63.32
        mulx      r11, rax, QWORD PTR [-280+rbp]                #61.33
        mov       edx, r8d                                      #65.30
        adcx      r15, r11                                      #64.32
        mov       r11d, r8d                                     #64.32
        setb      r11b                                          #64.32
        adox      edx, r8d                                      #65.30
        adox      r11, rax                                      #65.30
        mov       eax, r8d                                      #65.30
        seto      al                                            #65.30
        clc                                                     #66.34
        adcx      rsi, r12                                      #66.34
        mov       r12, -1                                       #71.35
        mov       rdx, rsi                                      #71.35
        adcx      rdi, r14                                      #67.34
        mov       r14, 0x0ffffffff                              #72.35
        adcx      r10, r13                                      #68.34
        mov       r13, 0xffffffff00000001                       #73.35
        adcx      r9, r15                                       #69.34
        mov       r15d, r8d                                     #70.34
        adcx      rcx, r11                                      #70.34
        setb      r15b                                          #70.34
        mov       DWORD PTR [-272+rbp], r15d                    #70.34[spill]
        mulx      rax, r15, r12                                 #71.35
        mulx      r12, r11, r14                                 #72.35
        mulx      r14, r13, r13                                 #73.35
        mov       edx, r8d                                      #74.34
        adox      edx, r8d                                      #74.34
        mov       rdx, QWORD PTR [-288+rbp]                     #84.35
        adox      r15, r12                                      #74.34
        mov       r12d, 0                                       #75.34
        adox      r11, r12                                      #75.34
        adox      r14, r12                                      #76.34
        mov       r12d, r8d                                     #76.34
        seto      r12b                                          #76.34
        clc                                                     #77.31
        adcx      r12, r13                                      #77.31
        mov       r13d, r8d                                     #78.31
        adox      r13d, r8d                                     #78.31
        adox      rsi, rax                                      #78.31
        mulx      rax, r13, QWORD PTR [-296+rbp]                #85.35
        adox      rdi, r15                                      #79.34
        adox      r10, r11                                      #80.34
        mulx      r11, r15, rdx                                 #86.35
        adox      r9, r14                                       #81.34
        mov       r14d, r8d                                     #82.34
        adox      rcx, r12                                      #82.34
        mulx      rsi, r12, QWORD PTR [-304+rbp]                #84.35
        seto      r14b                                          #82.34
        clc                                                     #88.34
        adcx      r12, rax                                      #88.34
        adcx      r13, r11                                      #89.34
        mulx      r11, rax, QWORD PTR [-280+rbp]                #87.35
        mov       edx, r8d                                      #91.31
        adcx      r15, r11                                      #90.34
        mov       r11d, r8d                                     #90.34
        setb      r11b                                          #90.34
        adox      edx, r8d                                      #91.31
        adox      r11, rax                                      #91.31
        clc                                                     #92.34
        mov       eax, DWORD PTR [-272+rbp]                     #96.34[spill]
        adcx      rdi, rsi                                      #92.34
        mov       esi, r8d                                      #95.34
        mov       rdx, rdi                                      #97.35
        adcx      r10, r12                                      #93.34
        adcx      r9, r13                                       #94.34
        adcx      rcx, r15                                      #95.34
        setb      sil                                           #95.34
        mov       r15, -1                                       #95.34
        add       eax, r14d                                     #96.34
        cmp       r8d, esi                                      #96.34
        mov       r14, 0x0ffffffff                              #98.35
        mulx      r15, rsi, r15                                 #97.35
        adcx      rax, r11                                      #96.34
        mov       r11d, r8d                                     #96.34
        setb      r11b                                          #96.34
        mov       DWORD PTR [-264+rbp], r11d                    #96.34[spill]
        mulx      r11, r12, r14                                 #98.35
        mov       r14, 0xffffffff00000001                       #99.35
        mulx      r14, r13, r14                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-280+rbp]                     #110.35
        adox      rsi, r11                                      #100.34
        mov       r11d, 0                                       #101.34
        adox      r12, r11                                      #101.34
        adox      r14, r11                                      #102.34
        mov       r11d, r8d                                     #102.34
        seto      r11b                                          #102.34
        clc                                                     #103.31
        adcx      r11, r13                                      #103.31
        mov       r13d, r8d                                     #104.31
        adox      r13d, r8d                                     #104.31
        adox      rdi, r15                                      #104.31
        adox      r10, rsi                                      #105.34
        mulx      r15, rsi, QWORD PTR [-304+rbp]                #110.35
        adox      r9, r12                                       #106.34
        mov       r12d, r8d                                     #108.34
        adox      rcx, r14                                      #107.34
        mulx      rdi, r14, QWORD PTR [-296+rbp]                #111.35
        adox      rax, r11                                      #108.34
        mulx      r11, r13, QWORD PTR [-288+rbp]                #112.35
        seto      r12b                                          #108.34
        clc                                                     #114.34
        adcx      rsi, rdi                                      #114.34
        adcx      r14, r11                                      #115.34
        mulx      rdi, r11, rdx                                 #113.35
        mov       edx, r8d                                      #117.31
        adcx      r13, rdi                                      #116.34
        mov       edi, r8d                                      #116.34
        setb      dil                                           #116.34
        adox      edx, r8d                                      #117.31
        adox      rdi, r11                                      #117.31
        clc                                                     #118.34
        mov       r11d, DWORD PTR [-264+rbp]                    #122.34[spill]
        adcx      r10, r15                                      #118.34
        mov       r15d, r8d                                     #121.34
        mov       rdx, r10                                      #123.35
        adcx      r9, rsi                                       #119.34
        adcx      rcx, r14                                      #120.34
        adcx      rax, r13                                      #121.34
        mov       r13, 0x0ffffffff                              #124.35
        setb      r15b                                          #121.34
        xor       esi, esi                                      #121.34
        add       r11d, r12d                                    #122.34
        mov       r12, -1                                       #122.34
        cmp       r8d, r15d                                     #122.34
        adcx      r11, rdi                                      #122.34
        mov       rdi, 0xffffffff00000001                       #125.35
        setb      sil                                           #122.34
        mov       DWORD PTR [-256+rbp], esi                     #122.34[spill]
        mulx      r14, rsi, r12                                 #123.35
        mulx      r12, r15, r13                                 #124.35
        mulx      rdi, r13, rdi                                 #125.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      rsi, r12                                      #126.34
        mov       r12d, 0                                       #127.34
        adox      r15, r12                                      #127.34
        adox      rdi, r12                                      #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r14                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      r9, rsi                                       #131.34
        mov       r14d, DWORD PTR [-256+rbp]                    #140.31[spill]
        adox      rcx, r15                                      #132.34
        mov       r15, r9                                       #136.34
        adox      rax, rdi                                      #133.34
        mov       rdi, 0xffffffff00000001                       #139.34
        adox      r11, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       rsi, -1                                       #134.34
        add       r14d, r10d                                    #140.31
        sub       r15, rsi                                      #136.34
        mov       rsi, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       rsi, rdx                                      #137.34
        mov       rdx, r11                                      #139.34
        sbb       r10, r12                                      #138.34
        sbb       rdx, rdi                                      #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       r14, r12                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq r11, rdx;
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, rsi;
        testq r8, r8;
        cmovnzq r9, r15;
        mov       QWORD PTR [-152+rbp], r15                     #9.0
        mov       QWORD PTR [-176+rbp], rdx                     #207.37
        mov       QWORD PTR [-168+rbp], r10                     #207.37
        mov       QWORD PTR [-160+rbp], rsi                     #207.37
        vmovups   YMMWORD PTR [-208+rbp], ymm0                  #208.20
        mov       rdx, QWORD PTR [-336+rbp]                     #208.59
        mov       r15, 0x0ffffffff                              #47.33
        xor       r14d, r14d                                    #42.32
        xor       r13d, r13d                                    #42.32
        xor       r8d, r8d                                      #42.32
        mulx      rsi, r9, QWORD PTR [-328+rbp]                 #39.33
        mulx      r12, rdi, rdx                                 #38.33
        adcx      rdi, rsi                                      #42.32
        mulx      rcx, r10, QWORD PTR [-320+rbp]                #40.33
        adcx      r9, rcx                                       #43.32
        mov       rcx, -1                                       #46.33
        mulx      rax, r11, QWORD PTR [-312+rbp]                #41.33
        mov       rdx, r12                                      #46.33
        adcx      r10, rax                                      #44.32
        mulx      rax, r15, r15                                 #47.33
        setb      r14b                                          #44.32
        adox      r13d, r8d                                     #45.30
        adox      r14, r11                                      #45.30
        mulx      r13, r11, rcx                                 #46.33
        mov       ecx, 0                                        #50.32
        clc                                                     #49.32
        mov       rsi, 0xffffffff00000001                       #48.33
        adcx      r11, rax                                      #49.32
        mulx      rax, rsi, rsi                                 #48.33
        mov       edx, r8d                                      #52.30
        adcx      r15, rcx                                      #50.32
        adcx      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        setb      cl                                            #51.32
        adox      edx, r8d                                      #52.30
        adox      rcx, rsi                                      #52.30
        mov       rdx, QWORD PTR [-328+rbp]                     #58.33
        clc                                                     #53.30
        adcx      r12, r13                                      #53.30
        mov       r13d, r8d                                     #62.32
        adcx      rdi, r11                                      #54.32
        adcx      r9, r15                                       #55.32
        adcx      r10, rax                                      #56.32
        mulx      rax, r12, rdx                                 #59.33
        adcx      r14, rcx                                      #57.32
        mov       QWORD PTR [-240+rbp], r14                     #57.32[spill]
        mov       r14d, r8d                                     #57.32
        setb      r14b                                          #57.32
        adox      r13d, r8d                                     #62.32
        mov       r13d, 0                                       #75.34
        mov       QWORD PTR [-232+rbp], r14                     #70.34[spill]
        mulx      r14, r15, QWORD PTR [-336+rbp]                #58.33
        adox      r15, rax                                      #62.32
        mov       eax, r8d                                      #64.32
        mulx      r11, rcx, QWORD PTR [-320+rbp]                #60.33
        adox      r12, r11                                      #63.32
        mulx      rdx, rsi, QWORD PTR [-312+rbp]                #61.33
        adox      rcx, rdx                                      #64.32
        seto      al                                            #64.32
        clc                                                     #65.30
        adcx      rax, rsi                                      #65.30
        mov       esi, r8d                                      #66.34
        adox      esi, r8d                                      #66.34
        mov       rsi, QWORD PTR [-240+rbp]                     #69.34[spill]
        adox      rdi, r14                                      #66.34
        mov       r14, QWORD PTR [-232+rbp]                     #70.34[spill]
        mov       rdx, rdi                                      #71.35
        adox      r9, r15                                       #67.34
        mov       r15, 0x0ffffffff                              #72.35
        adox      r10, r12                                      #68.34
        mov       r12d, r8d                                     #70.34
        adox      rsi, rcx                                      #69.34
        mov       rcx, -1                                       #71.35
        adox      r14, rax                                      #70.34
        seto      r12b                                          #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-224+rbp], r12d                    #70.34[spill]
        mulx      r12, rax, rcx                                 #71.35
        mulx      rcx, r11, r15                                 #72.35
        mov       r15, 0xffffffff00000001                       #73.35
        adcx      rax, rcx                                      #74.34
        mulx      r15, rcx, r15                                 #73.35
        mov       edx, r8d                                      #77.31
        adcx      r11, r13                                      #75.34
        adcx      r15, r13                                      #76.34
        mov       r13d, r8d                                     #76.34
        setb      r13b                                          #76.34
        adox      edx, r8d                                      #77.31
        adox      r13, rcx                                      #77.31
        mov       rdx, QWORD PTR [-320+rbp]                     #84.35
        clc                                                     #78.31
        adcx      rdi, r12                                      #78.31
        mov       edi, r8d                                      #82.34
        adcx      r9, rax                                       #79.34
        mulx      rax, r12, QWORD PTR [-328+rbp]                #85.35
        adcx      r10, r11                                      #80.34
        adcx      rsi, r15                                      #81.34
        adcx      r14, r13                                      #82.34
        mov       r13d, r8d                                     #88.34
        mov       QWORD PTR [-232+rbp], r14                     #82.34[spill]
        setb      dil                                           #82.34
        adox      r13d, r8d                                     #88.34
        mulx      r14, r15, QWORD PTR [-336+rbp]                #84.35
        adox      r15, rax                                      #88.34
        mov       DWORD PTR [-216+rbp], edi                     #82.34[spill]
        mulx      r11, rdi, rdx                                 #86.35
        adox      r12, r11                                      #89.34
        mov       r11d, r8d                                     #90.34
        mulx      rdx, rcx, QWORD PTR [-312+rbp]                #87.35
        adox      rdi, rdx                                      #90.34
        seto      r11b                                          #90.34
        clc                                                     #91.31
        adcx      r11, rcx                                      #91.31
        mov       ecx, r8d                                      #92.34
        adox      ecx, r8d                                      #92.34
        mov       rcx, QWORD PTR [-232+rbp]                     #95.34[spill]
        adox      r9, r14                                       #92.34
        mov       r14d, r8d                                     #95.34
        mov       eax, DWORD PTR [-224+rbp]                     #96.34[spill]
        mov       rdx, r9                                       #97.35
        adox      r10, r15                                      #93.34
        adox      rsi, r12                                      #94.34
        adox      rcx, rdi                                      #95.34
        mov       rdi, 0x0ffffffff                              #98.35
        seto      r14b                                          #95.34
        xor       r15d, r15d                                    #95.34
        mov       r12, -1                                       #95.34
        add       eax, DWORD PTR [-216+rbp]                     #96.34[spill]
        cmp       r8d, r14d                                     #96.34
        mov       r14, 0xffffffff00000001                       #99.35
        adcx      rax, r11                                      #96.34
        mulx      r11, rdi, rdi                                 #98.35
        setb      r15b                                          #96.34
        mov       DWORD PTR [-144+rbp], r15d                    #96.34[spill]
        mulx      r15, r13, r12                                 #97.35
        mulx      r14, r12, r14                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-312+rbp]                     #110.35
        adox      r13, r11                                      #100.34
        mov       r11d, 0                                       #101.34
        adox      rdi, r11                                      #101.34
        adox      r14, r11                                      #102.34
        mov       r11d, r8d                                     #102.34
        seto      r11b                                          #102.34
        clc                                                     #103.31
        adcx      r11, r12                                      #103.31
        mov       r12d, r8d                                     #104.31
        adox      r12d, r8d                                     #104.31
        mov       r12d, r8d                                     #108.34
        adox      r9, r15                                       #104.31
        adox      r10, r13                                      #105.34
        adox      rsi, rdi                                      #106.34
        mulx      r9, rdi, QWORD PTR [-328+rbp]                 #111.35
        adox      rcx, r14                                      #107.34
        mulx      r14, r15, QWORD PTR [-336+rbp]                #110.35
        adox      rax, r11                                      #108.34
        mulx      r11, r13, QWORD PTR [-320+rbp]                #112.35
        seto      r12b                                          #108.34
        clc                                                     #114.34
        adcx      r15, r9                                       #114.34
        adcx      rdi, r11                                      #115.34
        mulx      r9, r11, rdx                                  #113.35
        mov       edx, r8d                                      #117.31
        adcx      r13, r9                                       #116.34
        mov       r9d, r8d                                      #116.34
        setb      r9b                                           #116.34
        adox      edx, r8d                                      #117.31
        adox      r9, r11                                       #117.31
        clc                                                     #118.34
        mov       r11d, DWORD PTR [-144+rbp]                    #122.34[spill]
        adcx      r10, r14                                      #118.34
        mov       rdx, r10                                      #123.35
        adcx      rsi, r15                                      #119.34
        mov       r15, -1                                       #123.35
        adcx      rcx, rdi                                      #120.34
        mulx      r15, rdi, r15                                 #123.35
        adcx      rax, r13                                      #121.34
        mov       r13d, r8d                                     #121.34
        setb      r13b                                          #121.34
        xor       r14d, r14d                                    #121.34
        add       r11d, r12d                                    #122.34
        cmp       r8d, r13d                                     #122.34
        mov       r12, 0x0ffffffff                              #124.35
        adcx      r11, r9                                       #122.34
        mov       r9, 0xffffffff00000001                        #125.35
        mulx      r9, r13, r9                                   #125.35
        setb      r14b                                          #122.34
        mov       DWORD PTR [-136+rbp], r14d                    #122.34[spill]
        mulx      r12, r14, r12                                 #124.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      rdi, r12                                      #126.34
        mov       r12d, 0                                       #127.34
        adox      r14, r12                                      #127.34
        adox      r9, r12                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r15                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      rsi, rdi                                      #131.34
        mov       edi, DWORD PTR [-136+rbp]                     #140.31[spill]
        adox      rcx, r14                                      #132.34
        mov       r14, rsi                                      #136.34
        adox      rax, r9                                       #133.34
        mov       r9, 0xffffffff00000001                        #139.34
        adox      r11, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       r15, -1                                       #134.34
        add       edi, r10d                                     #140.31
        sub       r14, r15                                      #136.34
        mov       r15, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       r15, rdx                                      #137.34
        mov       rdx, r11                                      #139.34
        sbb       r10, r12                                      #138.34
        sbb       rdx, r9                                       #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       rdi, r12                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq r11, rdx;
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, r15;
        testq r8, r8;
        cmovnzq rsi, r14;
        mov       QWORD PTR [-184+rbp], r14                     #9.0
        mov       QWORD PTR [-208+rbp], rdx                     #208.37
        mov       QWORD PTR [-200+rbp], r10                     #208.37
        mov       QWORD PTR [-192+rbp], r15                     #208.37
        vmovups   YMMWORD PTR [-272+rbp], ymm0                  #209.21
        mov       rdx, QWORD PTR [-176+rbp]                     #209.61
        mov       r15, 0x0ffffffff                              #47.33
        xor       r14d, r14d                                    #42.32
        xor       r13d, r13d                                    #42.32
        xor       r8d, r8d                                      #42.32
        mulx      r12, rdi, QWORD PTR [-304+rbp]                #38.33
        mulx      rsi, r9, QWORD PTR [-296+rbp]                 #39.33
        adcx      rdi, rsi                                      #42.32
        mulx      rcx, r10, QWORD PTR [-288+rbp]                #40.33
        adcx      r9, rcx                                       #43.32
        mov       rcx, -1                                       #46.33
        mulx      rax, r11, QWORD PTR [-280+rbp]                #41.33
        mov       rdx, r12                                      #46.33
        adcx      r10, rax                                      #44.32
        mulx      rax, r15, r15                                 #47.33
        setb      r14b                                          #44.32
        adox      r13d, r8d                                     #45.30
        adox      r14, r11                                      #45.30
        mulx      r13, r11, rcx                                 #46.33
        mov       ecx, 0                                        #50.32
        clc                                                     #49.32
        mov       rsi, 0xffffffff00000001                       #48.33
        adcx      r11, rax                                      #49.32
        mulx      rax, rsi, rsi                                 #48.33
        mov       edx, r8d                                      #52.30
        adcx      r15, rcx                                      #50.32
        adcx      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        setb      cl                                            #51.32
        adox      edx, r8d                                      #52.30
        adox      rcx, rsi                                      #52.30
        mov       rdx, QWORD PTR [-168+rbp]                     #58.33
        clc                                                     #53.30
        adcx      r12, r13                                      #53.30
        mov       r13d, r8d                                     #62.32
        adcx      rdi, r11                                      #54.32
        adcx      r9, r15                                       #55.32
        adcx      r10, rax                                      #56.32
        mulx      rax, r12, QWORD PTR [-296+rbp]                #59.33
        adcx      r14, rcx                                      #57.32
        mov       QWORD PTR [-144+rbp], r14                     #57.32[spill]
        mov       r14d, r8d                                     #57.32
        setb      r14b                                          #57.32
        adox      r13d, r8d                                     #62.32
        mov       r13d, 0                                       #75.34
        mov       QWORD PTR [-136+rbp], r14                     #70.34[spill]
        mulx      r14, r15, QWORD PTR [-304+rbp]                #58.33
        adox      r15, rax                                      #62.32
        mov       eax, r8d                                      #64.32
        mulx      r11, rcx, QWORD PTR [-288+rbp]                #60.33
        adox      r12, r11                                      #63.32
        mulx      rdx, rsi, QWORD PTR [-280+rbp]                #61.33
        adox      rcx, rdx                                      #64.32
        seto      al                                            #64.32
        clc                                                     #65.30
        adcx      rax, rsi                                      #65.30
        mov       esi, r8d                                      #66.34
        adox      esi, r8d                                      #66.34
        mov       rsi, QWORD PTR [-144+rbp]                     #69.34[spill]
        adox      rdi, r14                                      #66.34
        mov       r14, QWORD PTR [-136+rbp]                     #70.34[spill]
        mov       rdx, rdi                                      #71.35
        adox      r9, r15                                       #67.34
        mov       r15, 0x0ffffffff                              #72.35
        adox      r10, r12                                      #68.34
        mov       r12d, r8d                                     #70.34
        adox      rsi, rcx                                      #69.34
        mov       rcx, -1                                       #71.35
        adox      r14, rax                                      #70.34
        seto      r12b                                          #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-128+rbp], r12d                    #70.34[spill]
        mulx      r12, rax, rcx                                 #71.35
        mulx      rcx, r11, r15                                 #72.35
        mov       r15, 0xffffffff00000001                       #73.35
        adcx      rax, rcx                                      #74.34
        mulx      r15, rcx, r15                                 #73.35
        mov       edx, r8d                                      #77.31
        adcx      r11, r13                                      #75.34
        adcx      r15, r13                                      #76.34
        mov       r13d, r8d                                     #76.34
        setb      r13b                                          #76.34
        adox      edx, r8d                                      #77.31
        adox      r13, rcx                                      #77.31
        mov       rdx, QWORD PTR [-160+rbp]                     #84.35
        clc                                                     #78.31
        adcx      rdi, r12                                      #78.31
        mov       edi, r8d                                      #82.34
        adcx      r9, rax                                       #79.34
        mulx      rax, r12, QWORD PTR [-296+rbp]                #85.35
        adcx      r10, r11                                      #80.34
        adcx      rsi, r15                                      #81.34
        adcx      r14, r13                                      #82.34
        mov       r13d, r8d                                     #88.34
        mov       QWORD PTR [-136+rbp], r14                     #82.34[spill]
        setb      dil                                           #82.34
        adox      r13d, r8d                                     #88.34
        mulx      r14, r15, QWORD PTR [-304+rbp]                #84.35
        adox      r15, rax                                      #88.34
        mov       DWORD PTR [-120+rbp], edi                     #82.34[spill]
        mulx      r11, rdi, QWORD PTR [-288+rbp]                #86.35
        adox      r12, r11                                      #89.34
        mov       r11d, r8d                                     #90.34
        mulx      rdx, rcx, QWORD PTR [-280+rbp]                #87.35
        adox      rdi, rdx                                      #90.34
        seto      r11b                                          #90.34
        clc                                                     #91.31
        adcx      r11, rcx                                      #91.31
        mov       ecx, r8d                                      #92.34
        adox      ecx, r8d                                      #92.34
        mov       rcx, QWORD PTR [-136+rbp]                     #95.34[spill]
        adox      r9, r14                                       #92.34
        mov       r14d, r8d                                     #95.34
        mov       eax, DWORD PTR [-128+rbp]                     #96.34[spill]
        mov       rdx, r9                                       #97.35
        adox      r10, r15                                      #93.34
        adox      rsi, r12                                      #94.34
        adox      rcx, rdi                                      #95.34
        mov       rdi, 0x0ffffffff                              #98.35
        seto      r14b                                          #95.34
        xor       r15d, r15d                                    #95.34
        mov       r12, -1                                       #95.34
        add       eax, DWORD PTR [-120+rbp]                     #96.34[spill]
        cmp       r8d, r14d                                     #96.34
        mov       r14, 0xffffffff00000001                       #99.35
        adcx      rax, r11                                      #96.34
        mulx      r11, rdi, rdi                                 #98.35
        setb      r15b                                          #96.34
        mov       DWORD PTR [-72+rbp], r15d                     #96.34[spill]
        mulx      r15, r13, r12                                 #97.35
        mulx      r14, r12, r14                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-152+rbp]                     #110.35
        adox      r13, r11                                      #100.34
        mov       r11d, 0                                       #101.34
        adox      rdi, r11                                      #101.34
        adox      r14, r11                                      #102.34
        mov       r11d, r8d                                     #102.34
        seto      r11b                                          #102.34
        clc                                                     #103.31
        adcx      r11, r12                                      #103.31
        mov       r12d, r8d                                     #104.31
        adox      r12d, r8d                                     #104.31
        mov       r12d, r8d                                     #108.34
        adox      r9, r15                                       #104.31
        adox      r10, r13                                      #105.34
        adox      rsi, rdi                                      #106.34
        mulx      r9, rdi, QWORD PTR [-296+rbp]                 #111.35
        adox      rcx, r14                                      #107.34
        mulx      r14, r15, QWORD PTR [-304+rbp]                #110.35
        adox      rax, r11                                      #108.34
        mulx      r11, r13, QWORD PTR [-288+rbp]                #112.35
        seto      r12b                                          #108.34
        clc                                                     #114.34
        adcx      r15, r9                                       #114.34
        adcx      rdi, r11                                      #115.34
        mulx      r9, r11, QWORD PTR [-280+rbp]                 #113.35
        mov       edx, r8d                                      #117.31
        adcx      r13, r9                                       #116.34
        mov       r9d, r8d                                      #116.34
        setb      r9b                                           #116.34
        adox      edx, r8d                                      #117.31
        adox      r9, r11                                       #117.31
        clc                                                     #118.34
        mov       r11d, DWORD PTR [-72+rbp]                     #122.34[spill]
        adcx      r10, r14                                      #118.34
        mov       rdx, r10                                      #123.35
        adcx      rsi, r15                                      #119.34
        mov       r15, -1                                       #123.35
        adcx      rcx, rdi                                      #120.34
        mulx      r15, rdi, r15                                 #123.35
        adcx      rax, r13                                      #121.34
        mov       r13d, r8d                                     #121.34
        setb      r13b                                          #121.34
        xor       r14d, r14d                                    #121.34
        add       r11d, r12d                                    #122.34
        cmp       r8d, r13d                                     #122.34
        mov       r12, 0x0ffffffff                              #124.35
        adcx      r11, r9                                       #122.34
        mov       r9, 0xffffffff00000001                        #125.35
        mulx      r9, r13, r9                                   #125.35
        setb      r14b                                          #122.34
        mov       DWORD PTR [-64+rbp], r14d                     #122.34[spill]
        mulx      r12, r14, r12                                 #124.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      rdi, r12                                      #126.34
        mov       r12d, 0                                       #127.34
        adox      r14, r12                                      #127.34
        adox      r9, r12                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r15                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      rsi, rdi                                      #131.34
        mov       edi, DWORD PTR [-64+rbp]                      #140.31[spill]
        adox      rcx, r14                                      #132.34
        mov       r14, rsi                                      #136.34
        adox      rax, r9                                       #133.34
        mov       r9, 0xffffffff00000001                        #139.34
        adox      r11, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       r15, -1                                       #134.34
        add       edi, r10d                                     #140.31
        sub       r14, r15                                      #136.34
        mov       r15, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       r15, rdx                                      #137.34
        mov       rdx, r11                                      #139.34
        sbb       r10, r12                                      #138.34
        sbb       rdx, r9                                       #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       rdi, r12                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq r11, rdx;
        mov       r11d, 1                                       #9.0
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, r15;
        testq r8, r8;
        cmovnzq rsi, r14;
        mov       rsi, QWORD PTR [-96+rbp]                      #9.0[spill]
        mov       rdi, QWORD PTR [-112+rbp]                     #9.0[spill]
        mov       QWORD PTR [-248+rbp], r14                     #9.0
        mov       r14, 0xffffffff00000000                       #9.0
        mov       QWORD PTR [-272+rbp], rdx                     #209.35
        mov       QWORD PTR [-264+rbp], r10                     #209.35
        mov       QWORD PTR [-256+rbp], r15                     #209.35
        mov       rax, QWORD PTR [88+rsi]                       #9.0
        testq rdi, rdi;
        cmovnzq rax, r11;
        mov       rax, -1                                       #9.0
        mov       QWORD PTR [88+rsi], r11                       #210.5
        mov       rdx, QWORD PTR [80+rsi]                       #9.0
        testq rdi, rdi;
        cmovnzq rdx, r14;
        mov       rdx, -1                                       #9.0
        mov       QWORD PTR [80+rsi], r14                       #211.5
        mov       rcx, QWORD PTR [72+rsi]                       #9.0
        testq rdi, rdi;
        cmovnzq rcx, rax;
        mov       QWORD PTR [72+rsi], rax                       #212.5
        mov       r9, QWORD PTR [64+rsi]                        #9.0
        testq rdi, rdi;
        cmovnzq r9, rdx;
        mov       r10, QWORD PTR [-88+rbp]                      #9.0[spill]
        mov       QWORD PTR [64+rsi], rdx                       #213.5
        mov       r13, QWORD PTR [-80+rbp]                      #9.0[spill]
        mov       r12, QWORD PTR [88+r10]                       #9.0
        testq r13, r13;
        cmovnzq r11, r12;
        mov       QWORD PTR [88+rsi], r12                       #9.0
        mov       r11, QWORD PTR [80+r10]                       #9.0
        testq r13, r13;
        cmovnzq r14, r11;
        mov       QWORD PTR [80+rsi], r11                       #9.0
        mov       r12, QWORD PTR [72+r10]                       #9.0
        testq r13, r13;
        cmovnzq rax, r12;
        mov       QWORD PTR [72+rsi], r12                       #9.0
        mov       rcx, QWORD PTR [64+r10]                       #9.0
        testq r13, r13;
        cmovnzq rdx, rcx;
        mov       QWORD PTR [64+rsi], rcx                       #9.0
        vmovups   YMMWORD PTR [-240+rbp], ymm0                  #218.21
        mov       r8, r10                                       #38.33
        mov       rdx, QWORD PTR [-176+rbp]                     #218.60
        xor       r14d, r14d                                    #42.32
        xor       r13d, r13d                                    #42.32
        xor       esi, esi                                      #42.32
        mulx      r12, rdi, QWORD PTR [r8]                      #38.33
        mulx      rcx, r9, QWORD PTR [8+r8]                     #39.33
        adcx      rdi, rcx                                      #42.32
        mov       rcx, -1                                       #46.33
        mulx      rax, r10, QWORD PTR [16+r8]                   #40.33
        adcx      r9, rax                                       #43.32
        mov       rax, 0x0ffffffff                              #47.33
        mulx      r15, r11, QWORD PTR [24+r8]                   #41.33
        mov       r8d, 0                                        #44.32
        adcx      r10, r15                                      #44.32
        setb      r14b                                          #44.32
        mov       rdx, r12                                      #46.33
        adox      r13d, r8d                                     #45.30
        adox      r14, r11                                      #45.30
        mulx      r13, r11, rcx                                 #46.33
        mov       ecx, 0                                        #50.32
        seto      sil                                           #45.30
        clc                                                     #49.32
        mulx      rsi, r15, rax                                 #47.33
        adcx      r11, rsi                                      #49.32
        mov       rsi, 0xffffffff00000001                       #48.33
        mulx      rax, rsi, rsi                                 #48.33
        mov       edx, r8d                                      #52.30
        adcx      r15, rcx                                      #50.32
        adcx      rax, rcx                                      #51.32
        mov       ecx, r8d                                      #51.32
        setb      cl                                            #51.32
        adox      edx, r8d                                      #52.30
        adox      rcx, rsi                                      #52.30
        mov       rdx, QWORD PTR [-168+rbp]                     #58.33
        clc                                                     #53.30
        adcx      r12, r13                                      #53.30
        mov       r13, QWORD PTR [-88+rbp]                      #58.33[spill]
        adcx      rdi, r11                                      #54.32
        adcx      r9, r15                                       #55.32
        mov       r15d, r8d                                     #57.32
        adcx      r10, rax                                      #56.32
        mulx      rax, r11, QWORD PTR [8+r13]                   #59.33
        adcx      r14, rcx                                      #57.32
        mov       QWORD PTR [-304+rbp], r14                     #57.32[spill]
        setb      r15b                                          #57.32
        mov       QWORD PTR [-296+rbp], r15                     #70.34[spill]
        mulx      r12, r14, QWORD PTR [r13]                     #58.33
        mulx      r15, rcx, QWORD PTR [16+r13]                  #60.33
        mulx      rdx, rsi, QWORD PTR [24+r13]                  #61.33
        mov       r13d, r8d                                     #62.32
        adox      r13d, r8d                                     #62.32
        mov       r13d, 0                                       #75.34
        adox      r14, rax                                      #62.32
        mov       eax, r8d                                      #64.32
        adox      r11, r15                                      #63.32
        mov       r15d, r8d                                     #66.34
        adox      rcx, rdx                                      #64.32
        seto      al                                            #64.32
        clc                                                     #65.30
        adcx      rax, rsi                                      #65.30
        adox      r15d, r8d                                     #66.34
        mov       rsi, QWORD PTR [-304+rbp]                     #69.34[spill]
        mov       r15, 0xffffffff00000001                       #73.35
        adox      rdi, r12                                      #66.34
        mov       r12d, r8d                                     #70.34
        mov       rdx, rdi                                      #71.35
        adox      r9, r14                                       #67.34
        mov       r14, QWORD PTR [-296+rbp]                     #70.34[spill]
        adox      r10, r11                                      #68.34
        mov       r11, 0x0ffffffff                              #72.35
        adox      rsi, rcx                                      #69.34
        mov       rcx, -1                                       #71.35
        adox      r14, rax                                      #70.34
        seto      r12b                                          #70.34
        clc                                                     #74.34
        mov       DWORD PTR [-288+rbp], r12d                    #70.34[spill]
        mulx      r12, rax, rcx                                 #71.35
        mulx      rcx, r11, r11                                 #72.35
        adcx      rax, rcx                                      #74.34
        mulx      r15, rcx, r15                                 #73.35
        mov       edx, r8d                                      #77.31
        adcx      r11, r13                                      #75.34
        adcx      r15, r13                                      #76.34
        mov       r13d, r8d                                     #76.34
        setb      r13b                                          #76.34
        adox      edx, r8d                                      #77.31
        adox      r13, rcx                                      #77.31
        mov       rdx, QWORD PTR [-160+rbp]                     #84.35
        clc                                                     #78.31
        adcx      rdi, r12                                      #78.31
        mov       edi, r8d                                      #82.34
        adcx      r9, rax                                       #79.34
        adcx      r10, r11                                      #80.34
        adcx      rsi, r15                                      #81.34
        adcx      r14, r13                                      #82.34
        mov       r13, QWORD PTR [-88+rbp]                      #84.35[spill]
        setb      dil                                           #82.34
        mov       QWORD PTR [-296+rbp], r14                     #82.34[spill]
        mov       DWORD PTR [-280+rbp], edi                     #82.34[spill]
        mulx      r12, r14, QWORD PTR [r13]                     #84.35
        mulx      rax, r11, QWORD PTR [8+r13]                   #85.35
        mulx      r15, rdi, QWORD PTR [16+r13]                  #86.35
        mulx      rdx, rcx, QWORD PTR [24+r13]                  #87.35
        mov       r13d, r8d                                     #88.34
        adox      r13d, r8d                                     #88.34
        mov       r13d, r8d                                     #90.34
        adox      r14, rax                                      #88.34
        adox      r11, r15                                      #89.34
        mov       r15d, r8d                                     #95.34
        adox      rdi, rdx                                      #90.34
        seto      r13b                                          #90.34
        clc                                                     #91.31
        adcx      r13, rcx                                      #91.31
        mov       ecx, r8d                                      #92.34
        adox      ecx, r8d                                      #92.34
        mov       rcx, QWORD PTR [-296+rbp]                     #95.34[spill]
        adox      r9, r12                                       #92.34
        mov       eax, DWORD PTR [-288+rbp]                     #96.34[spill]
        mov       rdx, r9                                       #97.35
        adox      r10, r14                                      #93.34
        mov       r14, 0x0ffffffff                              #98.35
        adox      rsi, r11                                      #94.34
        adox      rcx, rdi                                      #95.34
        seto      r15b                                          #95.34
        xor       r12d, r12d                                    #95.34
        mov       rdi, -1                                       #95.34
        add       eax, DWORD PTR [-280+rbp]                     #96.34[spill]
        cmp       r8d, r15d                                     #96.34
        adcx      rax, r13                                      #96.34
        mulx      r15, r13, rdi                                 #97.35
        setb      r12b                                          #96.34
        mov       DWORD PTR [-72+rbp], r12d                     #96.34[spill]
        mov       r12, 0xffffffff00000001                       #99.35
        mulx      r14, rdi, r14                                 #98.35
        mulx      r11, r12, r12                                 #99.35
        mov       edx, r8d                                      #100.34
        adox      edx, r8d                                      #100.34
        mov       rdx, QWORD PTR [-152+rbp]                     #110.35
        adox      r13, r14                                      #100.34
        mov       r14d, 0                                       #101.34
        adox      rdi, r14                                      #101.34
        adox      r11, r14                                      #102.34
        mov       r14d, r8d                                     #102.34
        seto      r14b                                          #102.34
        clc                                                     #103.31
        adcx      r14, r12                                      #103.31
        mov       r12d, r8d                                     #104.31
        adox      r12d, r8d                                     #104.31
        mov       r12, QWORD PTR [-88+rbp]                      #110.35[spill]
        adox      r9, r15                                       #104.31
        mov       r9d, r8d                                      #108.34
        adox      r10, r13                                      #105.34
        mulx      r13, r15, QWORD PTR [r12]                     #110.35
        adox      rsi, rdi                                      #106.34
        adox      rcx, r11                                      #107.34
        adox      rax, r14                                      #108.34
        mulx      r11, r14, QWORD PTR [8+r12]                   #111.35
        seto      r9b                                           #108.34
        clc                                                     #114.34
        adcx      r15, r11                                      #114.34
        mulx      r11, rdi, QWORD PTR [16+r12]                  #112.35
        adcx      r14, r11                                      #115.34
        mulx      r12, r11, QWORD PTR [24+r12]                  #113.35
        mov       edx, r8d                                      #117.31
        adcx      rdi, r12                                      #116.34
        mov       r12d, r8d                                     #116.34
        setb      r12b                                          #116.34
        adox      edx, r8d                                      #117.31
        adox      r12, r11                                      #117.31
        clc                                                     #118.34
        adcx      r10, r13                                      #118.34
        mov       rdx, r10                                      #123.35
        adcx      rsi, r15                                      #119.34
        mov       r15d, r8d                                     #121.34
        adcx      rcx, r14                                      #120.34
        mov       r14, 0x0ffffffff                              #124.35
        adcx      rax, rdi                                      #121.34
        mov       edi, DWORD PTR [-72+rbp]                      #122.34[spill]
        setb      r15b                                          #121.34
        add       edi, r9d                                      #122.34
        xor       r9d, r9d                                      #122.34
        cmp       r8d, r15d                                     #122.34
        mov       r15, -1                                       #123.35
        adcx      rdi, r12                                      #122.34
        mulx      r12, r11, r15                                 #123.35
        setb      r9b                                           #122.34
        mov       DWORD PTR [-64+rbp], r9d                      #122.34[spill]
        mov       r9, 0xffffffff00000001                        #125.35
        mulx      r14, r15, r14                                 #124.35
        mulx      r9, r13, r9                                   #125.35
        mov       edx, r8d                                      #126.34
        adox      edx, r8d                                      #126.34
        mov       edx, r8d                                      #128.34
        adox      r11, r14                                      #126.34
        mov       r14d, 0                                       #127.34
        adox      r15, r14                                      #127.34
        adox      r9, r14                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r13                                      #129.31
        mov       r13d, r8d                                     #130.31
        adox      r13d, r8d                                     #130.31
        adox      r10, r12                                      #130.31
        mov       r10d, r8d                                     #134.34
        adox      rsi, r11                                      #131.34
        mov       r11d, DWORD PTR [-64+rbp]                     #140.31[spill]
        adox      rcx, r15                                      #132.34
        mov       r15, rsi                                      #136.34
        adox      rax, r9                                       #133.34
        mov       r9, 0xffffffff00000001                        #139.34
        adox      rdi, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r10b                                          #134.34
        xor       r13d, r13d                                    #134.34
        mov       r12, -1                                       #134.34
        add       r11d, r10d                                    #140.31
        sub       r15, r12                                      #136.34
        mov       r12, rcx                                      #137.34
        mov       r10, rax                                      #138.34
        sbb       r12, rdx                                      #137.34
        mov       rdx, rdi                                      #139.34
        sbb       r10, r14                                      #138.34
        sbb       rdx, r9                                       #139.34
        setb      r13b                                          #139.34
        cmp       r8d, r13d                                     #140.31
        sbb       r11, r14                                      #140.31
        setb      r8b                                           #140.31
        testq r8, r8;
        cmovnzq rdi, rdx;
        testq r8, r8;
        cmovnzq rax, r10;
        testq r8, r8;
        cmovnzq rcx, r12;
        testq r8, r8;
        cmovnzq rsi, r15;
        mov       QWORD PTR [-152+rbp], r15                     #9.0
        mov       QWORD PTR [-176+rbp], rdx                     #218.35
        mov       QWORD PTR [-168+rbp], r10                     #218.35
        mov       QWORD PTR [-160+rbp], r12                     #218.35
        vmovups   YMMWORD PTR [-144+rbp], ymm0                  #219.21
        mov       r12, QWORD PTR [-240+rbp]                     #219.64
        xor       r8d, r8d                                      #21.32
        xor       edi, edi                                      #18.32
        xor       r13d, r13d                                    #18.32
        mov       r11, QWORD PTR [-232+rbp]                     #219.88
        adcx      r12, r12                                      #18.32
        mov       r15, 0x0ffffffff                              #23.32
        mov       r10, QWORD PTR [-224+rbp]                     #219.80
        mov       rsi, r12                                      #22.32
        adcx      r11, r11                                      #19.32
        mov       r13, 0xffffffff00000001                       #25.32
        mov       r9, QWORD PTR [-216+rbp]                      #219.72
        mov       rcx, r11                                      #23.32
        adcx      r10, r10                                      #20.32
        mov       rdx, r10                                      #24.32
        adcx      r9, r9                                        #21.32
        mov       rax, r9                                       #25.32
        setb      dil                                           #21.32
        mov       r14, -1                                       #21.32
        sub       rsi, r14                                      #22.32
        mov       r14d, 0                                       #24.32
        sbb       rcx, r15                                      #23.32
        sbb       rdx, r14                                      #24.32
        sbb       rax, r13                                      #25.32
        sbb       rdi, r14                                      #26.30
        setb      r8b                                           #26.30
        testq r8, r8;
        cmovnzq r9, rax;
        testq r8, r8;
        cmovnzq r10, rdx;
        testq r8, r8;
        cmovnzq r11, rcx;
        testq r8, r8;
        cmovnzq r12, rsi;
        mov       QWORD PTR [-120+rbp], rsi                     #9.0
        mov       QWORD PTR [-144+rbp], rax                     #219.35
        mov       QWORD PTR [-136+rbp], rdx                     #219.35
        mov       QWORD PTR [-128+rbp], rcx                     #219.35
        vmovups   YMMWORD PTR [-176+rbp], ymm0                  #220.20
        mov       r13, QWORD PTR [-208+rbp]                     #159.32
        xor       r10d, r10d                                    #162.32
        xor       r15d, r15d                                    #159.32
        sub       r13, QWORD PTR [-144+rbp]                     #159.32
        mov       r14, QWORD PTR [-200+rbp]                     #160.32
        sbb       r14, QWORD PTR [-136+rbp]                     #160.32
        mov       r12, QWORD PTR [-192+rbp]                     #161.32
        sbb       r12, QWORD PTR [-128+rbp]                     #161.32
        mov       r11, QWORD PTR [-184+rbp]                     #162.32
        mov       r8, 0xffffffff00000001                        #170.30
        sbb       r11, QWORD PTR [-120+rbp]                     #162.32
        setb      r15b                                          #162.32
        mov       rsi, -1                                       #162.32
        xor       edi, edi                                      #162.32
        xor       r9d, r9d                                      #162.32
        xor       ecx, ecx                                      #162.32
        testq r15, r15;
        cmovnzq rsi, rdi;
        xor       eax, eax                                      #165.32
        mov       edx, edi                                      #167.32
        adox      r13, rdi                                      #165.32
        mov       QWORD PTR [-152+rbp], r13                     #220.34
        adox      r14, rdx                                      #167.32
        mov       QWORD PTR [-160+rbp], r14                     #220.34
        adox      r12, r9                                       #168.32
        mov       QWORD PTR [-168+rbp], r12                     #220.34
        seto      cl                                            #168.32
        mov       rdx, -1                                       #168.32
        and       rdi, r8                                       #170.30
        cmp       r10d, ecx                                     #170.30
        adcx      r11, rdi                                      #170.30
        xor       edi, edi                                      #9.0
        mov       QWORD PTR [-176+rbp], r11                     #220.34
        sub       r11, QWORD PTR [-272+rbp]                     #159.32
        sbb       r12, QWORD PTR [-264+rbp]                     #160.32
        sbb       r14, QWORD PTR [-256+rbp]                     #161.32
        sbb       r13, QWORD PTR [-248+rbp]                     #162.32
        setb      al                                            #162.32
        testq rax, rax;
        cmovnzq rdx, rdi;
        xor       r15d, r15d                                    #165.32
        mov       ecx, edi                                      #167.32
        adox      r11, rdi                                      #165.32
        mov       rsi, QWORD PTR [-96+rbp]                      #174.1[spill]
        adox      r12, rcx                                      #167.32
        mov       QWORD PTR [24+rsi], r11                       #174.1
        adox      r14, r9                                       #168.32
        mov       r9d, r10d                                     #168.32
        mov       QWORD PTR [8+rsi], r14                        #172.1
        seto      r9b                                           #168.32
        and       rdi, r8                                       #170.30
        cmp       r10d, r9d                                     #170.30
        mov       r8, QWORD PTR [-104+rbp]                      #9.0[spill]
        adcx      r13, rdi                                      #170.30
        mov       QWORD PTR [16+rsi], r12                       #173.1
        mov       QWORD PTR [rsi], r13                          #171.1
        mov       rcx, QWORD PTR [24+r8]                        #9.0
        mov       rdi, QWORD PTR [-112+rbp]                     #9.0[spill]
        testq rdi, rdi;
        cmovnzq r11, rcx;
        mov       QWORD PTR [24+rsi], rcx                       #222.5
        mov       rdx, QWORD PTR [16+r8]                        #9.0
        testq rdi, rdi;
        cmovnzq r12, rdx;
        mov       QWORD PTR [16+rsi], rdx                       #223.5
        mov       rax, QWORD PTR [8+r8]                         #9.0
        testq rdi, rdi;
        cmovnzq r14, rax;
        mov       QWORD PTR [8+rsi], rax                        #224.5
        mov       r8, QWORD PTR [r8]                            #9.0
        testq rdi, rdi;
        cmovnzq r13, r8;
        mov       r14, QWORD PTR [-88+rbp]                      #9.0[spill]
        mov       QWORD PTR [rsi], r8                           #225.5
        mov       rdi, QWORD PTR [-80+rbp]                      #9.0[spill]
        mov       r13, QWORD PTR [24+r14]                       #9.0
        testq rdi, rdi;
        cmovnzq rcx, r13;
        mov       QWORD PTR [24+rsi], r13                       #9.0
        mov       r11, QWORD PTR [16+r14]                       #9.0
        testq rdi, rdi;
        cmovnzq rdx, r11;
        mov       QWORD PTR [16+rsi], r11                       #9.0
        mov       r12, QWORD PTR [8+r14]                        #9.0
        testq rdi, rdi;
        cmovnzq rax, r12;
        mov       QWORD PTR [8+rsi], r12                        #9.0
        mov       rax, QWORD PTR [r14]                          #9.0
        testq rdi, rdi;
        cmovnzq r8, rax;
        mov       QWORD PTR [rsi], rax                          #9.0
        vmovups   YMMWORD PTR [-304+rbp], ymm0                  #230.21
        mov       r10, r14                                      #38.33
        mov       r13, -1                                       #46.33
        mov       rdx, QWORD PTR [-272+rbp]                     #230.63
        xor       edi, edi                                      #42.32
        mov       r15, 0xffffffff00000001                       #48.33
        mulx      r11, rsi, QWORD PTR [32+r10]                  #38.33
        mulx      rcx, r8, QWORD PTR [40+r10]                   #39.33
        adox      rsi, rcx                                      #42.32
        mov       rcx, 0x0ffffffff                              #47.33
        mulx      rax, r9, QWORD PTR [48+r10]                   #40.33
        adox      r8, rax                                       #43.32
        mulx      r10, r12, QWORD PTR [56+r10]                  #41.33
        mov       rdx, r11                                      #46.33
        adox      r9, r10                                       #44.32
        mov       r10d, edi                                     #44.32
        mulx      rax, r15, r15                                 #48.33
        seto      r10b                                          #44.32
        clc                                                     #45.30
        adcx      r10, r12                                      #45.30
        mulx      r13, r12, r13                                 #46.33
        mulx      rcx, r14, rcx                                 #47.33
        mov       edx, edi                                      #49.32
        adox      edx, edi                                      #49.32
        mov       rdx, QWORD PTR [-264+rbp]                     #58.33
        adox      r12, rcx                                      #49.32
        mov       ecx, 0                                        #50.32
        adox      r14, rcx                                      #50.32
        adox      rax, rcx                                      #51.32
        mov       ecx, edi                                      #51.32
        seto      cl                                            #51.32
        clc                                                     #52.30
        adcx      rcx, r15                                      #52.30
        mov       r15d, edi                                     #53.30
        adox      r15d, edi                                     #53.30
        adox      r11, r13                                      #53.30
        adox      rsi, r12                                      #54.32
        adox      r8, r14                                       #55.32
        mov       r14, QWORD PTR [-88+rbp]                      #58.33[spill]
        adox      r9, rax                                       #56.32
        mulx      r15, rax, QWORD PTR [32+r14]                  #58.33
        adox      r10, rcx                                      #57.32
        mov       ecx, edi                                      #57.32
        mulx      r11, r12, QWORD PTR [40+r14]                  #59.33
        seto      cl                                            #57.32
        clc                                                     #62.32
        adcx      rax, r11                                      #62.32
        mulx      r13, r11, QWORD PTR [48+r14]                  #60.33
        adcx      r12, r13                                      #63.32
        mulx      r14, r13, QWORD PTR [56+r14]                  #61.33
        mov       edx, edi                                      #65.30
        adcx      r11, r14                                      #64.32
        mov       r14d, edi                                     #64.32
        setb      r14b                                          #64.32
        adox      edx, edi                                      #65.30
        adox      r14, r13                                      #65.30
        clc                                                     #66.34
        adcx      rsi, r15                                      #66.34
        mov       rdx, rsi                                      #71.35
        adcx      r8, rax                                       #67.34
        mov       eax, edi                                      #70.34
        adcx      r9, r12                                       #68.34
        mov       r12, 0x0ffffffff                              #72.35
        adcx      r10, r11                                      #69.34
        mov       r11, -1                                       #71.35
        mulx      r15, r13, r11                                 #71.35
        mov       r11, 0xffffffff00000001                       #73.35
        adcx      rcx, r14                                      #70.34
        setb      al                                            #70.34
        mov       DWORD PTR [-176+rbp], eax                     #70.34[spill]
        mulx      rax, r14, r12                                 #72.35
        mulx      r11, r12, r11                                 #73.35
        mov       edx, edi                                      #74.34
        adox      edx, edi                                      #74.34
        mov       rdx, QWORD PTR [-256+rbp]                     #84.35
        adox      r13, rax                                      #74.34
        mov       eax, 0                                        #75.34
        adox      r14, rax                                      #75.34
        adox      r11, rax                                      #76.34
        mov       eax, edi                                      #76.34
        seto      al                                            #76.34
        clc                                                     #77.31
        adcx      rax, r12                                      #77.31
        mov       r12d, edi                                     #78.31
        adox      r12d, edi                                     #78.31
        adox      rsi, r15                                      #78.31
        mov       esi, edi                                      #82.34
        adox      r8, r13                                       #79.34
        adox      r9, r14                                       #80.34
        adox      r10, r11                                      #81.34
        mov       r11, QWORD PTR [-88+rbp]                      #84.35[spill]
        adox      rcx, rax                                      #82.34
        mulx      rax, r15, QWORD PTR [32+r11]                  #84.35
        seto      sil                                           #82.34
        clc                                                     #88.34
        mulx      r13, r14, QWORD PTR [40+r11]                  #85.35
        adcx      r15, r13                                      #88.34
        mulx      r12, r13, QWORD PTR [48+r11]                  #86.35
        adcx      r14, r12                                      #89.34
        mulx      r11, r12, QWORD PTR [56+r11]                  #87.35
        mov       edx, edi                                      #91.31
        adcx      r13, r11                                      #90.34
        mov       r11d, edi                                     #90.34
        setb      r11b                                          #90.34
        adox      edx, edi                                      #91.31
        adox      r11, r12                                      #91.31
        clc                                                     #92.34
        adcx      r8, rax                                       #92.34
        mov       eax, DWORD PTR [-176+rbp]                     #96.34[spill]
        mov       rdx, r8                                       #97.35
        adcx      r9, r15                                       #93.34
        mov       r15, 0x0ffffffff                              #98.35
        adcx      r10, r14                                      #94.34
        mov       r14d, edi                                     #95.34
        adcx      rcx, r13                                      #95.34
        setb      r14b                                          #95.34
        add       eax, esi                                      #96.34
        xor       esi, esi                                      #96.34
        cmp       edi, r14d                                     #96.34
        mov       r14, 0xffffffff00000001                       #99.35
        adcx      rax, r11                                      #96.34
        mov       r11, -1                                       #97.35
        mulx      r13, r14, r14                                 #99.35
        setb      sil                                           #96.34
        mov       DWORD PTR [-168+rbp], esi                     #96.34[spill]
        mulx      rsi, r12, r11                                 #97.35
        mulx      r15, r11, r15                                 #98.35
        mov       edx, edi                                      #100.34
        adox      edx, edi                                      #100.34
        mov       rdx, QWORD PTR [-248+rbp]                     #110.35
        adox      r12, r15                                      #100.34
        mov       r15d, 0                                       #101.34
        adox      r11, r15                                      #101.34
        adox      r13, r15                                      #102.34
        mov       r15d, edi                                     #102.34
        seto      r15b                                          #102.34
        clc                                                     #103.31
        adcx      r15, r14                                      #103.31
        mov       r14d, edi                                     #104.31
        adox      r14d, edi                                     #104.31
        mov       r14, QWORD PTR [-88+rbp]                      #110.35[spill]
        adox      r8, rsi                                       #104.31
        mov       r8d, edi                                      #108.34
        adox      r9, r12                                       #105.34
        mulx      rsi, r12, QWORD PTR [32+r14]                  #110.35
        adox      r10, r11                                      #106.34
        adox      rcx, r13                                      #107.34
        adox      rax, r15                                      #108.34
        mulx      r13, r15, QWORD PTR [40+r14]                  #111.35
        seto      r8b                                           #108.34
        clc                                                     #114.34
        adcx      r12, r13                                      #114.34
        mulx      r13, r11, QWORD PTR [48+r14]                  #112.35
        adcx      r15, r13                                      #115.34
        mulx      r14, r13, QWORD PTR [56+r14]                  #113.35
        mov       edx, edi                                      #117.31
        adcx      r11, r14                                      #116.34
        mov       r14d, edi                                     #116.34
        setb      r14b                                          #116.34
        adox      edx, edi                                      #117.31
        adox      r14, r13                                      #117.31
        clc                                                     #118.34
        adcx      r9, rsi                                       #118.34
        mov       rdx, r9                                       #123.35
        adcx      r10, r12                                      #119.34
        mov       r12d, edi                                     #121.34
        adcx      rcx, r15                                      #120.34
        mov       r15, 0x0ffffffff                              #124.35
        adcx      rax, r11                                      #121.34
        mov       r11d, DWORD PTR [-168+rbp]                    #122.34[spill]
        setb      r12b                                          #121.34
        add       r11d, r8d                                     #122.34
        xor       r8d, r8d                                      #122.34
        cmp       edi, r12d                                     #122.34
        mov       r12, -1                                       #123.35
        adcx      r11, r14                                      #122.34
        mulx      r14, r13, r12                                 #123.35
        setb      r8b                                           #122.34
        mov       DWORD PTR [-160+rbp], r8d                     #122.34[spill]
        mov       r8, 0xffffffff00000001                        #125.35
        mulx      r15, r12, r15                                 #124.35
        mulx      r8, rsi, r8                                   #125.35
        mov       edx, edi                                      #126.34
        adox      edx, edi                                      #126.34
        mov       edx, edi                                      #128.34
        adox      r13, r15                                      #126.34
        mov       r15d, 0                                       #127.34
        adox      r12, r15                                      #127.34
        adox      r8, r15                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, rsi                                      #129.31
        mov       esi, edi                                      #130.31
        adox      esi, edi                                      #130.31
        adox      r9, r14                                       #130.31
        mov       r9d, edi                                      #134.34
        adox      r10, r13                                      #131.34
        mov       r13d, DWORD PTR [-160+rbp]                    #140.31[spill]
        adox      rcx, r12                                      #132.34
        mov       r12, r10                                      #136.34
        adox      rax, r8                                       #133.34
        mov       r8, 0xffffffff00000001                        #139.34
        adox      r11, rdx                                      #134.34
        mov       rdx, 0x0ffffffff                              #137.34
        seto      r9b                                           #134.34
        xor       esi, esi                                      #134.34
        mov       r14, -1                                       #134.34
        add       r13d, r9d                                     #140.31
        sub       r12, r14                                      #136.34
        mov       r14, rcx                                      #137.34
        mov       r9, rax                                       #138.34
        sbb       r14, rdx                                      #137.34
        mov       rdx, r11                                      #139.34
        sbb       r9, r15                                       #138.34
        sbb       rdx, r8                                       #139.34
        setb      sil                                           #139.34
        cmp       edi, esi                                      #140.31
        sbb       r13, r15                                      #140.31
        setb      dil                                           #140.31
        testq rdi, rdi;
        cmovnzq r11, rdx;
        testq rdi, rdi;
        cmovnzq rax, r9;
        testq rdi, rdi;
        cmovnzq rcx, r14;
        testq rdi, rdi;
        cmovnzq r10, r12;
        mov       QWORD PTR [-280+rbp], r12                     #9.0
        mov       QWORD PTR [-304+rbp], rdx                     #230.34
        mov       QWORD PTR [-296+rbp], r9                      #230.34
        mov       QWORD PTR [-288+rbp], r14                     #230.34
        vmovups   YMMWORD PTR [-208+rbp], ymm0                  #231.21
        mov       rcx, QWORD PTR [-96+rbp]                      #159.32[spill]
        xor       eax, eax                                      #162.32
        mov       r9, QWORD PTR [-240+rbp]                      #159.32
        xor       esi, esi                                      #162.32
        mov       r11, QWORD PTR [-232+rbp]                     #160.32
        mov       rdi, -1                                       #9.0
        sub       r9, QWORD PTR [rcx]                           #159.32
        mov       r13, QWORD PTR [-224+rbp]                     #161.32
        sbb       r11, QWORD PTR [8+rcx]                        #160.32
        mov       r14, 0xffffffff00000001                       #170.30
        mov       rdx, QWORD PTR [-216+rbp]                     #162.32
        sbb       r13, QWORD PTR [16+rcx]                       #161.32
        sbb       rdx, QWORD PTR [24+rcx]                       #162.32
        setb      sil                                           #162.32
        xor       r12d, r12d                                    #162.32
        xor       r15d, r15d                                    #162.32
        xor       ecx, ecx                                      #162.32
        testq rsi, rsi;
        cmovnzq rdi, rcx;
        xor       r8d, r8d                                      #165.32
        mov       r10d, ecx                                     #167.32
        adcx      r9, rcx                                       #165.32
        mov       QWORD PTR [-184+rbp], r9                      #231.34
        adcx      r11, r10                                      #167.32
        mov       QWORD PTR [-192+rbp], r11                     #231.34
        adcx      r13, r12                                      #168.32
        mov       QWORD PTR [-200+rbp], r13                     #231.34
        setb      r15b                                          #168.32
        and       rcx, r14                                      #170.30
        cmp       eax, r15d                                     #170.30
        adcx      rdx, rcx                                      #170.30
        mov       QWORD PTR [-208+rbp], rdx                     #231.34
        vmovups   YMMWORD PTR [-272+rbp], ymm0                  #232.21
        setb      al                                            #170.30
        mov       rdx, QWORD PTR [-208+rbp]                     #232.63
        mov       r15, -1                                       #46.33
        xor       esi, esi                                      #42.32
        xor       r10d, r10d                                    #42.32
        mov       rcx, 0xffffffff00000001                       #48.33
        mulx      r13, r8, QWORD PTR [-336+rbp]                 #38.33
        mulx      r12, r9, QWORD PTR [-328+rbp]                 #39.33
        adox      r8, r12                                       #42.32
        mov       r12d, r10d                                    #44.32
        mulx      rax, r11, QWORD PTR [-320+rbp]                #40.33
        adox      r9, rax                                       #43.32
        mov       rax, 0x0ffffffff                              #47.33
        mulx      rdi, r14, QWORD PTR [-312+rbp]                #41.33
        mov       rdx, r13                                      #46.33
        adox      r11, rdi                                      #44.32
        mulx      rdi, rax, rax                                 #47.33
        seto      r12b                                          #44.32
        clc                                                     #45.30
        adcx      r12, r14                                      #45.30
        mulx      r15, r14, r15                                 #46.33
        setb      sil                                           #45.30
        mulx      rsi, rcx, rcx                                 #48.33
        mov       edx, r10d                                     #49.32
        adox      edx, r10d                                     #49.32
        mov       rdx, QWORD PTR [-200+rbp]                     #58.33
        adox      r14, rdi                                      #49.32
        mov       edi, 0                                        #50.32
        adox      rax, rdi                                      #50.32
        adox      rsi, rdi                                      #51.32
        mov       edi, r10d                                     #51.32
        seto      dil                                           #51.32
        clc                                                     #52.30
        adcx      rdi, rcx                                      #52.30
        mov       ecx, r10d                                     #53.30
        adox      ecx, r10d                                     #53.30
        adox      r13, r15                                      #53.30
        mulx      r13, r15, QWORD PTR [-328+rbp]                #59.33
        adox      r8, r14                                       #54.32
        mulx      r14, rcx, QWORD PTR [-336+rbp]                #58.33
        adox      r9, rax                                       #55.32
        adox      r11, rsi                                      #56.32
        adox      r12, rdi                                      #57.32
        mov       edi, r10d                                     #57.32
        seto      dil                                           #57.32
        clc                                                     #62.32
        adcx      rcx, r13                                      #62.32
        mulx      rsi, r13, QWORD PTR [-320+rbp]                #60.33
        adcx      r15, rsi                                      #63.32
        mulx      rax, rsi, QWORD PTR [-312+rbp]                #61.33
        mov       edx, r10d                                     #65.30
        adcx      r13, rax                                      #64.32
        mov       eax, r10d                                     #64.32
        setb      al                                            #64.32
        adox      edx, r10d                                     #65.30
        adox      rax, rsi                                      #65.30
        clc                                                     #66.34
        adcx      r8, r14                                       #66.34
        mov       r14d, r10d                                    #70.34
        mov       rdx, r8                                       #71.35
        adcx      r9, rcx                                       #67.34
        adcx      r11, r15                                      #68.34
        mov       r15, 0x0ffffffff                              #72.35
        adcx      r12, r13                                      #69.34
        mov       r13, -1                                       #71.35
        mulx      rcx, rsi, r13                                 #71.35
        adcx      rdi, rax                                      #70.34
        mulx      rax, r13, r15                                 #72.35
        setb      r14b                                          #70.34
        mov       DWORD PTR [-240+rbp], r14d                    #70.34[spill]
        mov       r14, 0xffffffff00000001                       #73.35
        mulx      r14, r15, r14                                 #73.35
        mov       edx, r10d                                     #74.34
        adox      edx, r10d                                     #74.34
        mov       rdx, QWORD PTR [-192+rbp]                     #84.35
        adox      rsi, rax                                      #74.34
        mov       eax, 0                                        #75.34
        adox      r13, rax                                      #75.34
        adox      r14, rax                                      #76.34
        mov       eax, r10d                                     #76.34
        seto      al                                            #76.34
        clc                                                     #77.31
        adcx      rax, r15                                      #77.31
        mov       r15d, r10d                                    #78.31
        adox      r15d, r10d                                    #78.31
        adox      r8, rcx                                       #78.31
        mov       ecx, r10d                                     #82.34
        mulx      r8, r15, QWORD PTR [-328+rbp]                 #85.35
        adox      r9, rsi                                       #79.34
        adox      r11, r13                                      #80.34
        adox      r12, r14                                      #81.34
        mulx      r13, r14, QWORD PTR [-336+rbp]                #84.35
        adox      rdi, rax                                      #82.34
        seto      cl                                            #82.34
        clc                                                     #88.34
        adcx      r14, r8                                       #88.34
        mulx      rsi, r8, QWORD PTR [-320+rbp]                 #86.35
        adcx      r15, rsi                                      #89.34
        mulx      rax, rsi, QWORD PTR [-312+rbp]                #87.35
        mov       edx, r10d                                     #91.31
        adcx      r8, rax                                       #90.34
        mov       eax, r10d                                     #90.34
        setb      al                                            #90.34
        adox      edx, r10d                                     #91.31
        adox      rax, rsi                                      #91.31
        clc                                                     #92.34
        mov       esi, DWORD PTR [-240+rbp]                     #96.34[spill]
        adcx      r9, r13                                       #92.34
        mov       r13d, r10d                                    #95.34
        mov       rdx, r9                                       #97.35
        adcx      r11, r14                                      #93.34
        adcx      r12, r15                                      #94.34
        adcx      rdi, r8                                       #95.34
        setb      r13b                                          #95.34
        xor       r14d, r14d                                    #95.34
        mov       r8, -1                                        #95.34
        add       esi, ecx                                      #96.34
        cmp       r10d, r13d                                    #96.34
        mov       rcx, 0x0ffffffff                              #98.35
        mov       r13, 0xffffffff00000001                       #99.35
        adcx      rsi, rax                                      #96.34
        mulx      rcx, rax, rcx                                 #98.35
        setb      r14b                                          #96.34
        mov       DWORD PTR [-232+rbp], r14d                    #96.34[spill]
        mulx      r14, r8, r8                                   #97.35
        mulx      r13, r15, r13                                 #99.35
        mov       edx, r10d                                     #100.34
        adox      edx, r10d                                     #100.34
        mov       rdx, QWORD PTR [-184+rbp]                     #110.35
        adox      r8, rcx                                       #100.34
        mov       ecx, 0                                        #101.34
        adox      rax, rcx                                      #101.34
        adox      r13, rcx                                      #102.34
        mov       ecx, r10d                                     #102.34
        seto      cl                                            #102.34
        clc                                                     #103.31
        adcx      rcx, r15                                      #103.31
        mov       r15d, r10d                                    #104.31
        adox      r15d, r10d                                    #104.31
        adox      r9, r14                                       #104.31
        mulx      r9, r14, QWORD PTR [-328+rbp]                 #111.35
        adox      r11, r8                                       #105.34
        mulx      r15, r8, QWORD PTR [-336+rbp]                 #110.35
        adox      r12, rax                                      #106.34
        adox      rdi, r13                                      #107.34
        mov       r13d, r10d                                    #108.34
        adox      rsi, rcx                                      #108.34
        mulx      rcx, rax, QWORD PTR [-320+rbp]                #112.35
        seto      r13b                                          #108.34
        clc                                                     #114.34
        adcx      r8, r9                                        #114.34
        adcx      r14, rcx                                      #115.34
        mulx      r9, rcx, QWORD PTR [-312+rbp]                 #113.35
        mov       edx, r10d                                     #117.31
        adcx      rax, r9                                       #116.34
        mov       r9d, r10d                                     #116.34
        setb      r9b                                           #116.34
        adox      edx, r10d                                     #117.31
        adox      r9, rcx                                       #117.31
        clc                                                     #118.34
        mov       ecx, DWORD PTR [-232+rbp]                     #122.34[spill]
        adcx      r11, r15                                      #118.34
        mov       r15, 0x0ffffffff                              #124.35
        mov       rdx, r11                                      #123.35
        adcx      r12, r8                                       #119.34
        adcx      rdi, r14                                      #120.34
        adcx      rsi, rax                                      #121.34
        mov       eax, r10d                                     #121.34
        setb      al                                            #121.34
        xor       r8d, r8d                                      #121.34
        add       ecx, r13d                                     #122.34
        mov       r13, -1                                       #122.34
        cmp       r10d, eax                                     #122.34
        adcx      rcx, r9                                       #122.34
        mov       r9, 0xffffffff00000001                        #125.35
        setb      r8b                                           #122.34
        mov       DWORD PTR [-224+rbp], r8d                     #122.34[spill]
        mulx      r8, r14, r13                                  #123.35
        mulx      rax, r13, r15                                 #124.35
        mulx      r9, r15, r9                                   #125.35
        mov       edx, r10d                                     #126.34
        adox      edx, r10d                                     #126.34
        mov       edx, r10d                                     #128.34
        adox      r14, rax                                      #126.34
        mov       eax, 0                                        #127.34
        adox      r13, rax                                      #127.34
        adox      r9, rax                                       #128.34
        seto      dl                                            #128.34
        clc                                                     #129.31
        adcx      rdx, r15                                      #129.31
        mov       r15d, r10d                                    #130.31
        adox      r15d, r10d                                    #130.31
        adox      r11, r8                                       #130.31
        mov       r11d, r10d                                    #134.34
        adox      r12, r14                                      #131.34
        mov       r14, 0xffffffff00000001                       #139.34
        mov       r8, r12                                       #136.34
        adox      rdi, r13                                      #132.34
        adox      rsi, r9                                       #133.34
        mov       r9d, DWORD PTR [-224+rbp]                     #140.31[spill]
        adox      rcx, rdx                                      #134.34
        mov       r13, rcx                                      #139.34
        seto      r11b                                          #134.34
        xor       r15d, r15d                                    #134.34
        mov       rdx, -1                                       #134.34
        add       r9d, r11d                                     #140.31
        sub       r8, rdx                                       #136.34
        mov       rdx, rdi                                      #137.34
        mov       r11, 0x0ffffffff                              #137.34
        sbb       rdx, r11                                      #137.34
        mov       r11, rsi                                      #138.34
        sbb       r11, rax                                      #138.34
        sbb       r13, r14                                      #139.34
        setb      r15b                                          #139.34
        cmp       r10d, r15d                                    #140.31
        mov       r15d, r10d                                    #140.31
        sbb       r9, rax                                       #140.31
        setb      r15b                                          #140.31
        testq r15, r15;
        cmovnzq rcx, r13;
        xor       ecx, ecx                                      #9.0
        testq r15, r15;
        cmovnzq rsi, r11;
        testq r15, r15;
        cmovnzq rdi, rdx;
        mov       rdi, -1                                       #9.0
        testq r15, r15;
        cmovnzq r12, r8;
        xor       r12d, r12d                                    #162.32
        mov       QWORD PTR [-272+rbp], r13                     #232.34
        sub       r13, QWORD PTR [-304+rbp]                     #159.32
        mov       QWORD PTR [-264+rbp], r11                     #232.34
        sbb       r11, QWORD PTR [-296+rbp]                     #160.32
        mov       QWORD PTR [-256+rbp], rdx                     #232.34
        sbb       rdx, QWORD PTR [-288+rbp]                     #161.32
        mov       QWORD PTR [-248+rbp], r8                      #232.34
        sbb       r8, QWORD PTR [-280+rbp]                      #162.32
        setb      r12b                                          #162.32
        testq r12, r12;
        cmovnzq rdi, rcx;
        xor       esi, esi                                      #165.32
        mov       r12d, ecx                                     #167.32
        adcx      r13, rcx                                      #165.32
        mov       rsi, QWORD PTR [-112+rbp]                     #9.0[spill]
        adcx      r11, r12                                      #167.32
        mov       r12d, r10d                                    #168.32
        adcx      rdx, rax                                      #168.32
        mov       rax, QWORD PTR [-96+rbp]                      #172.1[spill]
        setb      r12b                                          #168.32
        and       r14, rcx                                      #170.30
        cmp       r10d, r12d                                    #170.30
        mov       rcx, QWORD PTR [-104+rbp]                     #9.0[spill]
        adcx      r8, r14                                       #170.30
        mov       QWORD PTR [40+rax], rdx                       #172.1
        mov       QWORD PTR [48+rax], r11                       #173.1
        mov       QWORD PTR [56+rax], r13                       #174.1
        mov       QWORD PTR [32+rax], r8                        #171.1
        mov       rdi, QWORD PTR [56+rcx]                       #9.0
        testq rsi, rsi;
        cmovnzq r13, rdi;
        mov       QWORD PTR [56+rax], rdi                       #234.5
        mov       r12, QWORD PTR [48+rcx]                       #9.0
        testq rsi, rsi;
        cmovnzq r11, r12;
        mov       QWORD PTR [48+rax], r12                       #235.5
        mov       r10, QWORD PTR [40+rcx]                       #9.0
        testq rsi, rsi;
        cmovnzq rdx, r10;
        mov       QWORD PTR [40+rax], r10                       #236.5
        mov       rcx, QWORD PTR [32+rcx]                       #9.0
        testq rsi, rsi;
        cmovnzq r8, rcx;
        mov       rsi, QWORD PTR [-88+rbp]                      #9.0[spill]
        mov       QWORD PTR [32+rax], rcx                       #237.5
        mov       rdx, QWORD PTR [-80+rbp]                      #9.0[spill]
        mov       r8, QWORD PTR [56+rsi]                        #9.0
        testq rdx, rdx;
        cmovnzq rdi, r8;
        mov       QWORD PTR [56+rax], r8                        #9.0
        mov       r13, QWORD PTR [48+rsi]                       #9.0
        testq rdx, rdx;
        cmovnzq r12, r13;
        mov       QWORD PTR [48+rax], r13                       #9.0
        mov       rdi, QWORD PTR [40+rsi]                       #9.0
        testq rdx, rdx;
        cmovnzq r10, rdi;
        mov       QWORD PTR [40+rax], rdi                       #9.0
        mov       r8, QWORD PTR [32+rsi]                        #9.0
        testq rdx, rdx;
        cmovnzq rcx, r8;
        mov       QWORD PTR [32+rax], r8                        #9.0
        vzeroupper                                              #242.1
        lea       rsp, QWORD PTR [-32+rbp]                      #242.1
        pop       r15                                           #242.1
        pop       r14                                           #242.1
        pop       r13                                           #242.1
        pop       r12                                           #242.1
        pop       rbp                                           #242.1
        mov       rsp, rbx                                      #242.1
        pop       rbx                                           #242.1
        ret                                                     #242.1
