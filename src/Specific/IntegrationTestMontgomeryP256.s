.intel_syntax noprefix
# icc17 -m64 -O3 -madx -march=skylake -mtune=skylake -fomit-frame-pointer -fno-stack-protector-all -opt-report
        push      r12                                           #11.1
        push      r13                                           #11.1
        push      r14                                           #11.1
        push      r15                                           #11.1
        push      rbx                                           #11.1
        push      rbp                                           #11.1
        mov       rbp, r8                                       #11.1
        mov       QWORD PTR [-32+rsp], rdx                      #11.1[spill]
        mov       rdx, rbp                                      #11.33
        mov       QWORD PTR [-24+rsp], rsi                      #11.1[spill]
        mov       r11, r9                                       #11.1
        mov       r12, -1                                       #15.32
        xor       esi, esi                                      #15.32
        mov       r9, rcx                                       #11.1
        mov       r8, QWORD PTR [72+rsp]                        #11.1
        mulx      rbx, rax, QWORD PTR [64+rsp]                  #12.33
        mov       QWORD PTR [-16+rsp], rdi                      #11.1[spill]
        mulx      rdi, r10, r8                                  #11.33
        adcx      r10, rbx                                      #15.32
        mov       ebx, esi                                      #18.30
        mulx      r14, rcx, QWORD PTR [56+rsp]                  #13.33
        adcx      rax, r14                                      #16.32
        mov       r14, 0xffffffff00000001                       #21.33
        mulx      rbp, r13, r11                                 #14.33
        mov       rdx, rdi                                      #19.33
        adcx      rcx, rbp                                      #17.32
        mov       ebp, esi                                      #17.32
        mov       QWORD PTR [-40+rsp], r11                      #11.1[spill]
        setb      bpl                                           #17.32
        adox      ebx, esi                                      #18.30
        adox      rbp, r13                                      #18.30
        mulx      r15, r11, r12                                 #19.33
        mov       rbx, 0x0ffffffff                              #20.33
        clc                                                     #22.32
        mulx      rbx, r12, rbx                                 #20.33
        adcx      r11, rbx                                      #22.32
        mov       ebx, 0                                        #23.32
        mulx      r13, r14, r14                                 #21.33
        mov       edx, esi                                      #25.30
        adcx      r12, rbx                                      #23.32
        adcx      r13, rbx                                      #24.32
        mov       ebx, esi                                      #24.32
        setb      bl                                            #24.32
        adox      edx, esi                                      #25.30
        mov       rdx, r9                                       #31.33
        adox      rbx, r14                                      #25.30
        mov       r14d, esi                                     #25.30
        seto      r14b                                          #25.30
        clc                                                     #26.30
        adcx      rdi, r15                                      #26.30
        mov       edi, esi                                      #35.32
        adcx      r10, r11                                      #27.32
        mulx      r14, r15, QWORD PTR [64+rsp]                  #32.33
        adcx      rax, r12                                      #28.32
        mulx      r12, r11, r8                                  #31.33
        adcx      rcx, r13                                      #29.32
        mulx      r13, r8, QWORD PTR [56+rsp]                   #33.33
        adcx      rbp, rbx                                      #30.32
        mov       ebx, esi                                      #30.32
        mulx      rdx, r9, QWORD PTR [-40+rsp]                  #34.33[spill]
        setb      bl                                            #30.32
        adox      edi, esi                                      #35.32
        adox      r11, r14                                      #35.32
        mov       r14d, esi                                     #39.34
        adox      r15, r13                                      #36.32
        mov       r13d, esi                                     #37.32
        adox      r8, rdx                                       #37.32
        seto      r13b                                          #37.32
        clc                                                     #38.30
        adcx      r13, r9                                       #38.30
        adox      r14d, esi                                     #39.34
        mov       r9, 0x0ffffffff                               #45.35
        mov       r14, 0xffffffff00000001                       #46.35
        adox      r10, r12                                      #39.34
        mov       rdx, r10                                      #44.35
        adox      rax, r11                                      #40.34
        mov       r11d, esi                                     #43.34
        mulx      r12, rdi, r9                                  #45.35
        adox      rcx, r15                                      #41.34
        mulx      r14, r9, r14                                  #46.35
        adox      rbp, r8                                       #42.34
        mov       r8, -1                                        #44.35
        adox      rbx, r13                                      #43.34
        mulx      r15, r13, r8                                  #44.35
        mov       r8d, 0                                        #48.34
        seto      r11b                                          #43.34
        clc                                                     #47.34
        mov       rdx, QWORD PTR [-32+rsp]                      #57.35[spill]
        adcx      r13, r12                                      #47.34
        mov       r12d, esi                                     #49.34
        adcx      rdi, r8                                       #48.34
        adcx      r14, r8                                       #49.34
        mov       r8d, esi                                      #50.31
        setb      r12b                                          #49.34
        adox      r8d, esi                                      #50.31
        adox      r12, r9                                       #50.31
        mov       r9d, esi                                      #50.31
        seto      r9b                                           #50.31
        clc                                                     #51.31
        mulx      r9, r8, QWORD PTR [56+rsp]                    #59.35
        adcx      r10, r15                                      #51.31
        mov       r10d, esi                                     #55.34
        adcx      rax, r13                                      #52.34
        adcx      rcx, rdi                                      #53.34
        mov       edi, esi                                      #61.34
        adcx      rbp, r14                                      #54.34
        mulx      r14, r13, QWORD PTR [72+rsp]                  #57.35
        adcx      rbx, r12                                      #55.34
        mulx      r15, r12, QWORD PTR [64+rsp]                  #58.35
        setb      r10b                                          #55.34
        adox      edi, esi                                      #61.34
        mov       DWORD PTR [-8+rsp], r10d                      #55.34[spill]
        mov       rdi, 0xffffffff00000001                       #72.35
        adox      r13, r15                                      #61.34
        mulx      rdx, r10, QWORD PTR [-40+rsp]                 #60.35[spill]
        adox      r12, r9                                       #62.34
        mov       r9d, esi                                      #63.34
        adox      r8, rdx                                       #63.34
        seto      r9b                                           #63.34
        clc                                                     #64.31
        adcx      r9, r10                                       #64.31
        mov       r10d, esi                                     #65.34
        adox      r10d, esi                                     #65.34
        mov       r10d, DWORD PTR [-8+rsp]                      #69.34[spill]
        adox      rax, r14                                      #65.34
        mov       r14d, esi                                     #68.34
        mov       rdx, rax                                      #70.35
        adox      rcx, r13                                      #66.34
        adox      rbp, r12                                      #67.34
        adox      rbx, r8                                       #68.34
        mov       r8, 0x0ffffffff                               #71.35
        seto      r14b                                          #68.34
        xor       r15d, r15d                                    #68.34
        add       r10d, r11d                                    #69.34
        mov       r11, -1                                       #69.34
        cmp       esi, r14d                                     #69.34
        mulx      r13, r12, r11                                 #70.35
        adcx      r10, r9                                       #69.34
        mulx      r9, r14, r8                                   #71.35
        mulx      r8, rdi, rdi                                  #72.35
        mov       edx, esi                                      #73.34
        setb      r15b                                          #69.34
        adox      edx, esi                                      #73.34
        mov       rdx, QWORD PTR [-24+rsp]                      #83.35[spill]
        adox      r12, r9                                       #73.34
        mov       r9d, 0                                        #74.34
        adox      r14, r9                                       #74.34
        adox      r8, r9                                        #75.34
        mov       r9d, esi                                      #75.34
        seto      r9b                                           #75.34
        clc                                                     #76.31
        adcx      r9, rdi                                       #76.31
        mov       edi, esi                                      #77.31
        adox      edi, esi                                      #77.31
        adox      rax, r13                                      #77.31
        mulx      r13, rax, QWORD PTR [64+rsp]                  #84.35
        adox      rcx, r12                                      #78.34
        adox      rbp, r14                                      #79.34
        mulx      r14, r12, QWORD PTR [72+rsp]                  #83.35
        adox      rbx, r8                                       #80.34
        adox      r10, r9                                       #81.34
        mov       r9d, esi                                      #81.34
        seto      r9b                                           #81.34
        clc                                                     #87.34
        adcx      r12, r13                                      #87.34
        mulx      r8, r13, QWORD PTR [56+rsp]                   #85.35
        adcx      rax, r8                                       #88.34
        mulx      r8, rdi, QWORD PTR [-40+rsp]                  #86.35[spill]
        mov       edx, esi                                      #90.31
        adcx      r13, r8                                       #89.34
        mov       r8d, esi                                      #89.34
        setb      r8b                                           #89.34
        adox      edx, esi                                      #90.31
        adox      r8, rdi                                       #90.31
        mov       edi, esi                                      #90.31
        seto      dil                                           #90.31
        clc                                                     #91.34
        adcx      rcx, r14                                      #91.34
        mov       rdx, rcx                                      #96.35
        adcx      rbp, r12                                      #92.34
        mov       r12, 0x0ffffffff                              #97.35
        mulx      rdi, r12, r12                                 #97.35
        adcx      rbx, rax                                      #93.34
        mov       eax, esi                                      #94.34
        adcx      r10, r13                                      #94.34
        setb      al                                            #94.34
        add       r9d, r15d                                     #95.31
        cmp       esi, eax                                      #95.31
        mov       rax, 0xffffffff00000001                       #98.35
        adcx      r9, r8                                        #95.31
        mulx      r8, r15, rax                                  #98.35
        mov       eax, 0                                        #100.34
        mulx      r14, r13, r11                                 #96.35
        mov       r11d, esi                                     #99.34
        adox      r11d, esi                                     #99.34
        adox      r13, rdi                                      #99.34
        mov       edi, esi                                      #101.34
        adox      r12, rax                                      #100.34
        adox      rax, r8                                       #101.34
        seto      dil                                           #101.34
        clc                                                     #102.31
        adcx      rdi, r15                                      #102.31
        mov       r15d, esi                                     #103.31
        adox      r15d, esi                                     #103.31
        adox      rcx, r14                                      #103.31
        mov       rcx, QWORD PTR [-16+rsp]                      #108.1[spill]
        adox      rbp, r13                                      #104.34
        mov       QWORD PTR [24+rcx], rbp                       #111.1
        adox      rbx, r12                                      #105.34
        mov       QWORD PTR [16+rcx], rbx                       #110.1
        adox      r10, rax                                      #106.34
        mov       QWORD PTR [8+rcx], r10                        #109.1
        adox      r9, rdi                                       #107.31
        mov       QWORD PTR [rcx], r9                           #108.1
        seto      sil                                           #107.31
        pop       rbp                                           #112.97
        pop       rbx                                           #112.97
        pop       r15                                           #112.97
        pop       r14                                           #112.97
        pop       r13                                           #112.97
        pop       r12                                           #112.97
        ret                                                     #112.97
