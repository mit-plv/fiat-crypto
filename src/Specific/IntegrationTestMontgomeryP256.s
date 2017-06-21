.intel_syntax noprefix
#icc17 -m64 -O3 -madx -march=skylake -mtune=skylake -fomit-frame-pointer -fno-stack-protector-all -opt-report
#IntegrationTestMontgomeryP256(unsigned long*, unsigned long, unsigned long, unsigned long, unsigned long, unsigned long, unsigned long, unsigned long, unsigned long):
        push      r12                                           #13.1
        push      r13                                           #13.1
        push      r14                                           #13.1
        push      r15                                           #13.1
        push      rbx                                           #13.1
        push      rbp                                           #13.1
        mov       rbx, r9                                       #13.1
        mov       QWORD PTR [-32+rsp], rdx                      #13.1[spill]
        mov       rdx, r8                                       #13.33
        mov       QWORD PTR [-16+rsp], rdi                      #13.1[spill]
        mov       r11, -1                                       #21.33
        xor       edi, edi                                      #17.32
        mov       r9, QWORD PTR [72+rsp]                        #13.1
        mulx      rax, rbp, QWORD PTR [64+rsp]                  #14.33
        mulx      r15, r10, r9                                  #13.33
        adcx      r10, rax                                      #17.32
        mov       rax, 0x0ffffffff                              #22.33
        mov       QWORD PTR [-24+rsp], rsi                      #13.1[spill]
        mulx      r14, rsi, QWORD PTR [56+rsp]                  #15.33
        adcx      rbp, r14                                      #18.32
        mulx      r8, r13, rbx                                  #16.33
        mov       rdx, r15                                      #21.33
        adcx      rsi, r8                                       #19.32
        mov       QWORD PTR [-40+rsp], rbx                      #13.1[spill]
        mov       ebx, 0                                        #19.32
        mov       r8d, ebx                                      #20.30
        setb      dil                                           #19.32
        adox      r8d, ebx                                      #20.30
        mov       r8d, ebx                                      #20.30
        adox      rdi, r13                                      #20.30
        mulx      r12, r11, r11                                 #21.33
        seto      r8b                                           #20.30
        clc                                                     #24.32
        mulx      r8, r13, rax                                  #22.33
        mov       rax, 0xffffffff00000001                       #23.33
        adcx      r11, r8                                       #24.32
        mov       r8d, 0                                        #25.32
        mulx      r14, rax, rax                                 #23.33
        mov       edx, ebx                                      #27.30
        adcx      r13, r8                                       #25.32
        adcx      r14, r8                                       #26.32
        mov       r8d, ebx                                      #26.32
        setb      r8b                                           #26.32
        adox      edx, ebx                                      #27.30
        mov       rdx, rcx                                      #33.33
        adox      r8, rax                                       #27.30
        mov       ecx, ebx                                      #37.32
        clc                                                     #28.30
        adcx      r15, r12                                      #28.30
        mulx      r12, rax, r9                                  #33.33
        adcx      r10, r11                                      #29.32
        adcx      rbp, r13                                      #30.32
        mulx      r13, r15, QWORD PTR [56+rsp]                  #35.33
        adcx      rsi, r14                                      #31.32
        mulx      r14, r9, QWORD PTR [64+rsp]                   #34.33
        adcx      rdi, r8                                       #32.32
        mov       r8d, ebx                                      #32.32
        mulx      rdx, r11, QWORD PTR [-40+rsp]                 #36.33[spill]
        setb      r8b                                           #32.32
        adox      ecx, ebx                                      #37.32
        mov       rcx, -1                                       #46.35
        adox      rax, r14                                      #37.32
        mov       r14d, ebx                                     #39.32
        adox      r9, r13                                       #38.32
        adox      r15, rdx                                      #39.32
        seto      r14b                                          #39.32
        clc                                                     #40.30
        adcx      r14, r11                                      #40.30
        mov       r11d, ebx                                     #41.34
        adox      r11d, ebx                                     #41.34
        mov       r11d, ebx                                     #45.34
        adox      r10, r12                                      #41.34
        mov       rdx, r10                                      #46.35
        adox      rbp, rax                                      #42.34
        mov       rax, 0x0ffffffff                              #47.35
        mulx      r12, rax, rax                                 #47.35
        adox      rsi, r9                                       #43.34
        mov       r9, 0xffffffff00000001                        #48.35
        adox      rdi, r15                                      #44.34
        adox      r8, r14                                       #45.34
        mulx      r14, r13, rcx                                 #46.35
        seto      r11b                                          #45.34
        clc                                                     #49.34
        mulx      r15, rcx, r9                                  #48.35
        mov       r9d, ebx                                      #52.31
        adcx      r13, r12                                      #49.34
        mov       r12d, 0                                       #50.34
        mov       rdx, QWORD PTR [-32+rsp]                      #59.35[spill]
        adcx      rax, r12                                      #50.34
        adcx      r15, r12                                      #51.34
        mov       r12d, ebx                                     #51.34
        setb      r12b                                          #51.34
        adox      r9d, ebx                                      #52.31
        adox      r12, rcx                                      #52.31
        clc                                                     #53.31
        adcx      r10, r14                                      #53.31
        mov       r10d, ebx                                     #57.34
        adcx      rbp, r13                                      #54.34
        mulx      r14, r13, QWORD PTR [72+rsp]                  #59.35
        adcx      rsi, rax                                      #55.34
        mulx      rax, r9, QWORD PTR [56+rsp]                   #61.35
        adcx      rdi, r15                                      #56.34
        mov       r15d, ebx                                     #63.34
        adcx      r8, r12                                       #57.34
        setb      r10b                                          #57.34
        adox      r15d, ebx                                     #63.34
        mov       DWORD PTR [-8+rsp], r10d                      #57.34[spill]
        mulx      r10, r12, QWORD PTR [64+rsp]                  #60.35
        adox      r13, r10                                      #63.34
        mov       r10d, ebx                                     #67.34
        mulx      rdx, rcx, QWORD PTR [-40+rsp]                 #62.35[spill]
        adox      r12, rax                                      #64.34
        mov       eax, ebx                                      #65.34
        adox      r9, rdx                                       #65.34
        seto      al                                            #65.34
        clc                                                     #66.31
        adcx      rax, rcx                                      #66.31
        adox      r10d, ebx                                     #67.34
        mov       ecx, DWORD PTR [-8+rsp]                       #71.34[spill]
        adox      rbp, r14                                      #67.34
        mov       r14d, ebx                                     #70.34
        mov       rdx, rbp                                      #72.35
        adox      rsi, r13                                      #68.34
        adox      rdi, r12                                      #69.34
        adox      r8, r9                                        #70.34
        mov       r9, 0xffffffff00000001                        #74.35
        mulx      r10, r9, r9                                   #74.35
        seto      r14b                                          #70.34
        xor       r15d, r15d                                    #70.34
        add       ecx, r11d                                     #71.34
        cmp       ebx, r14d                                     #71.34
        mov       r11, 0x0ffffffff                              #73.35
        mulx      r11, r14, r11                                 #73.35
        adcx      rcx, rax                                      #71.34
        mov       rax, -1                                       #72.35
        mulx      r13, r12, rax                                 #72.35
        mov       edx, ebx                                      #75.34
        setb      r15b                                          #71.34
        adox      edx, ebx                                      #75.34
        mov       rdx, QWORD PTR [-24+rsp]                      #85.35[spill]
        adox      r12, r11                                      #75.34
        mov       r11d, 0                                       #76.34
        adox      r14, r11                                      #76.34
        adox      r10, r11                                      #77.34
        mov       r11d, ebx                                     #77.34
        seto      r11b                                          #77.34
        clc                                                     #78.31
        adcx      r11, r9                                       #78.31
        mov       r9d, ebx                                      #79.31
        adox      r9d, ebx                                      #79.31
        adox      rbp, r13                                      #79.31
        mulx      r13, r9, QWORD PTR [64+rsp]                   #86.35
        adox      rsi, r12                                      #80.34
        adox      rdi, r14                                      #81.34
        adox      r8, r10                                       #82.34
        mov       r10d, ebx                                     #83.34
        adox      rcx, r11                                      #83.34
        mulx      r11, rbp, QWORD PTR [72+rsp]                  #85.35
        seto      r10b                                          #83.34
        clc                                                     #89.34
        adcx      rbp, r13                                      #89.34
        mulx      r14, r13, QWORD PTR [56+rsp]                  #87.35
        adcx      r9, r14                                       #90.34
        mulx      r14, r12, QWORD PTR [-40+rsp]                 #88.35[spill]
        mov       edx, ebx                                      #92.31
        adcx      r13, r14                                      #91.34
        mov       r14d, ebx                                     #91.34
        setb      r14b                                          #91.34
        adox      edx, ebx                                      #92.31
        adox      r14, r12                                      #92.31
        mov       r12d, ebx                                     #92.31
        seto      r12b                                          #92.31
        clc                                                     #93.34
        adcx      rsi, r11                                      #93.34
        mov       r11, 0x0ffffffff                              #99.35
        mov       rdx, rsi                                      #98.35
        adcx      rdi, rbp                                      #94.34
        mov       ebp, ebx                                      #96.34
        adcx      r8, r9                                        #95.34
        mulx      r9, r11, r11                                  #99.35
        adcx      rcx, r13                                      #96.34
        mulx      r12, r13, rax                                 #98.35
        setb      bpl                                           #96.34
        add       r10d, r15d                                    #97.34
        cmp       ebx, ebp                                      #97.34
        mov       rbp, 0xffffffff00000001                       #100.35
        mulx      rbp, r15, rbp                                 #100.35
        mov       edx, ebx                                      #101.34
        adcx      r10, r14                                      #97.34
        mov       r14d, ebx                                     #97.34
        setb      r14b                                          #97.34
        adox      edx, ebx                                      #101.34
        mov       edx, 0                                        #102.34
        adox      r13, r9                                       #101.34
        mov       r9d, ebx                                      #103.34
        adox      r11, rdx                                      #102.34
        adox      rbp, rdx                                      #103.34
        seto      r9b                                           #103.34
        clc                                                     #104.31
        adcx      r9, r15                                       #104.31
        mov       r15d, ebx                                     #105.31
        adox      r15d, ebx                                     #105.31
        adox      rsi, r12                                      #105.31
        mov       esi, ebx                                      #109.34
        adox      rdi, r13                                      #106.34
        adox      r8, r11                                       #107.34
        adox      rcx, rbp                                      #108.34
        adox      r10, r9                                       #109.34
        seto      sil                                           #109.34
        xor       ebp, ebp                                      #109.34
        add       esi, r14d                                     #110.26
        mov       rsi, QWORD PTR [-16+rsp]                      #122.1[spill]
        cmove     rax, rdx                                      #111.40
        sub       rdi, rax                                      #113.34
        mov       QWORD PTR [24+rsi], rdi                       #122.1
        mov       edi, eax                                      #115.34
        sbb       r8, rdi                                       #115.34
        mov       QWORD PTR [16+rsi], r8                        #121.1
        sbb       rcx, rdx                                      #116.34
        mov       rdx, 0xffffffff00000001                       #118.31
        mov       QWORD PTR [8+rsi], rcx                        #120.1
        setb      bpl                                           #116.34
        and       rdx, rax                                      #118.31
        cmp       ebx, ebp                                      #118.31
        sbb       r10, rdx                                      #118.31
        mov       QWORD PTR [rsi], r10                          #119.1
        pop       rbp                                           #123.106
        pop       rbx                                           #123.106
        pop       r15                                           #123.106
        pop       r14                                           #123.106
        pop       r13                                           #123.106
        pop       r12                                           #123.106
        ret                                                     #123.106
