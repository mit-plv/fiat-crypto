.section .text
.globl p256_jacobian_add_affine
.type p256_jacobian_add_affine, @function
p256_jacobian_add_affine:
        pushq     %r12                                          #197.3
        pushq     %r13                                          #197.3
        pushq     %r14                                          #197.3
        pushq     %r15                                          #197.3
        pushq     %rbx                                          #197.3
        pushq     %rbp                                          #197.3
        subq      $280, %rsp                                    #197.3
        movq      %rdx, 104(%rsp)                               #197.3[spill]
        pxor      %xmm0, %xmm0                                  #206.20
        movq      %rsi, 120(%rsp)                               #197.3[spill]
        movq      %rdi, 112(%rsp)                               #197.3[spill]
        movups    %xmm0, (%rsp)                                 #206.20
        movups    %xmm0, 16(%rsp)                               #206.20
        movq      %rsi, %r11                                    #206.41
        movq      $-1, %rsi                                     #80.34
        xorl      %edi, %edi                                    #76.32
        movq      $0x0ffffffff, %rdi                            #81.34
        vpxor     %xmm0, %xmm0, %xmm0                           #208.20
        movq      88(%r11), %r12                                #206.62
        movq      %r12, %rdx                                    #72.34
        movq      80(%r11), %r13                                #206.55
        movq      64(%r11), %r10                                #206.41
        movq      72(%r11), %r9                                 #206.48
        mulx      %r12, %r15, %r14                              #72.34
        mulx      %r13, %r11, %rax                              #73.34
        adcx      %r11, %r14                                    #76.32
        mulx      %r9, %rbx, %r8                                #74.34
        adcx      %rbx, %rax                                    #77.32
        movq      $0xffffffff00000001, %rbx                     #82.34
        mulx      %r10, %rcx, %rbp                              #75.34
        movq      %r15, %rdx                                    #80.34
        adcx      %rcx, %r8                                     #78.32
        movq      %r9, 168(%rsp)                                #206.48[spill]
        movl      $0, %r9d                                      #76.32
        movq      %r10, 88(%rsp)                                #206.41[spill]
        movl      %r9d, %r11d                                   #78.32
        movl      %r9d, %r10d                                   #79.30
        setb      %r11b                                         #78.32
        adox      %r9d, %r10d                                   #79.30
        adox      %rbp, %r11                                    #79.30
        mulx      %rsi, %rsi, %rbp                              #80.34
        clc                                                     #83.32
        mulx      %rdi, %r10, %rcx                              #81.34
        adcx      %r10, %rbp                                    #83.32
        movl      $0, %r10d                                     #84.32
        mulx      %rbx, %rbx, %rdi                              #82.34
        movl      %r9d, %edx                                    #86.30
        adcx      %r10, %rcx                                    #84.32
        movq      %r13, 176(%rsp)                               #206.55[spill]
        adcx      %r10, %rbx                                    #85.32
        movl      %r9d, %r10d                                   #85.32
        movq      %r12, 184(%rsp)                               #206.62[spill]
        setb      %r10b                                         #85.32
        adox      %r9d, %edx                                    #86.30
        movq      %r13, %rdx                                    #92.34
        adox      %rdi, %r10                                    #86.30
        movl      %r9d, %edi                                    #86.30
        seto      %dil                                          #86.30
        clc                                                     #87.30
        adcx      %rsi, %r15                                    #87.30
        adcx      %rbp, %r14                                    #88.32
        adcx      %rcx, %rax                                    #89.32
        mulx      %r13, %rcx, %r15                              #93.34
        movl      %r9d, %r13d                                   #96.32
        adcx      %rbx, %r8                                     #90.32
        mulx      %r12, %rsi, %rbx                              #92.34
        adcx      %r10, %r11                                    #91.32
        movl      %r9d, %r10d                                   #91.32
        mulx      168(%rsp), %rbp, %r12                         #94.34[spill]
        setb      %r10b                                         #91.32
        adox      %r9d, %r13d                                   #96.32
        mulx      88(%rsp), %rdx, %rdi                          #95.34[spill]
        adox      %rcx, %rbx                                    #96.32
        movl      %r9d, %ecx                                    #98.32
        adox      %rbp, %r15                                    #97.32
        movl      %r9d, %ebp                                    #100.34
        adox      %rdx, %r12                                    #98.32
        seto      %cl                                           #98.32
        clc                                                     #99.30
        adcx      %rdi, %rcx                                    #99.30
        adox      %r9d, %ebp                                    #100.34
        movl      %r9d, %edi                                    #104.34
        adox      %rsi, %r14                                    #100.34
        movq      %r14, %rdx                                    #105.36
        adox      %rbx, %rax                                    #101.34
        movq      $0x0ffffffff, %rbx                            #106.36
        adox      %r15, %r8                                     #102.34
        movq      $0xffffffff00000001, %r15                     #107.36
        adox      %r12, %r11                                    #103.34
        movq      $-1, %r12                                     #105.36
        mulx      %r12, %rbp, %r13                              #105.36
        movl      $0, %r12d                                     #109.34
        adox      %rcx, %r10                                    #104.34
        mulx      %rbx, %rsi, %rcx                              #106.36
        seto      %dil                                          #104.34
        clc                                                     #108.34
        adcx      %rsi, %r13                                    #108.34
        mulx      %r15, %rbx, %rsi                              #107.36
        movl      %r9d, %r15d                                   #110.34
        adcx      %r12, %rcx                                    #109.34
        movq      168(%rsp), %rdx                               #118.36[spill]
        adcx      %r12, %rbx                                    #110.34
        movl      %r9d, %r12d                                   #111.31
        setb      %r15b                                         #110.34
        adox      %r9d, %r12d                                   #111.31
        adox      %rsi, %r15                                    #111.31
        clc                                                     #112.31
        movl      %r9d, %esi                                    #122.34
        adcx      %rbp, %r14                                    #112.31
        movl      %r9d, %r14d                                   #116.34
        adcx      %r13, %rax                                    #113.34
        adcx      %rcx, %r8                                     #114.34
        mulx      176(%rsp), %rcx, %r12                         #119.36[spill]
        adcx      %rbx, %r11                                    #115.34
        adcx      %r15, %r10                                    #116.34
        mulx      184(%rsp), %r15, %r13                         #118.36[spill]
        setb      %r14b                                         #116.34
        adox      %r9d, %esi                                    #122.34
        movl      %r14d, 64(%rsp)                               #116.34[spill]
        movl      %r9d, %esi                                    #124.34
        adox      %rcx, %r13                                    #122.34
        movl      %r9d, %ecx                                    #125.31
        mulx      %rdx, %rbp, %r14                              #120.36
        adox      %rbp, %r12                                    #123.34
        movl      %r9d, %ebp                                    #126.34
        mulx      88(%rsp), %rdx, %rbx                          #121.36[spill]
        adox      %rdx, %r14                                    #124.34
        seto      %sil                                          #124.34
        clc                                                     #125.31
        adcx      %rbx, %rsi                                    #125.31
        movl      %r9d, %ebx                                    #129.34
        setb      %cl                                           #125.31
        adox      %r9d, %ebp                                    #126.34
        adox      %r15, %rax                                    #126.34
        movq      %rax, %rdx                                    #131.36
        adox      %r13, %r8                                     #127.34
        movq      $0x0ffffffff, %r13                            #132.36
        mulx      %r13, %r13, %r15                              #132.36
        adox      %r12, %r11                                    #128.34
        movq      $0xffffffff00000001, %r12                     #133.36
        adox      %r14, %r10                                    #129.34
        mulx      %r12, %r12, %r14                              #133.36
        seto      %bl                                           #129.34
        addl      64(%rsp), %edi                                #130.34[spill]
        cmpl      %ebx, %r9d                                    #130.34
        movl      %r9d, %ebx                                    #130.34
        adcx      %rsi, %rdi                                    #130.34
        movq      $-1, %rsi                                     #131.36
        mulx      %rsi, %rbp, %rcx                              #131.36
        movl      %r9d, %edx                                    #134.34
        setb      %bl                                           #130.34
        adox      %r9d, %edx                                    #134.34
        movq      88(%rsp), %rdx                                #144.36[spill]
        adox      %r13, %rcx                                    #134.34
        movl      $0, %r13d                                     #135.34
        adox      %r13, %r15                                    #135.34
        adox      %r13, %r12                                    #136.34
        movl      %r9d, %r13d                                   #136.34
        seto      %r13b                                         #136.34
        clc                                                     #137.31
        adcx      %r14, %r13                                    #137.31
        movl      %r9d, %r14d                                   #138.31
        adox      %r9d, %r14d                                   #138.31
        adox      %rbp, %rax                                    #138.31
        mulx      176(%rsp), %rax, %r14                         #145.36[spill]
        adox      %rcx, %r8                                     #139.34
        movl      %r9d, %ecx                                    #142.34
        adox      %r15, %r11                                    #140.34
        adox      %r12, %r10                                    #141.34
        adox      %r13, %rdi                                    #142.34
        mulx      184(%rsp), %r12, %r13                         #144.36[spill]
        seto      %cl                                           #142.34
        clc                                                     #148.34
        adcx      %rax, %r13                                    #148.34
        mulx      168(%rsp), %rax, %r15                         #146.36[spill]
        adcx      %rax, %r14                                    #149.34
        mulx      %rdx, %rax, %rbp                              #147.36
        movl      %r9d, %edx                                    #151.31
        adcx      %rax, %r15                                    #150.34
        movl      %r9d, %eax                                    #150.34
        setb      %al                                           #150.34
        adox      %r9d, %edx                                    #151.31
        adox      %rbp, %rax                                    #151.31
        clc                                                     #152.34
        adcx      %r12, %r8                                     #152.34
        movq      %r8, %rdx                                     #157.36
        adcx      %r13, %r11                                    #153.34
        adcx      %r14, %r10                                    #154.34
        movq      $0xffffffff00000001, %r14                     #159.36
        adcx      %r15, %rdi                                    #155.34
        movl      %r9d, %r15d                                   #155.34
        setb      %r15b                                         #155.34
        xorl      %ebp, %ebp                                    #155.34
        addl      %ecx, %ebx                                    #156.34
        cmpl      %r15d, %r9d                                   #156.34
        movq      $0x0ffffffff, %rcx                            #158.36
        mulx      %rsi, %r15, %r13                              #157.36
        adcx      %rax, %rbx                                    #156.34
        mulx      %rcx, %rcx, %r12                              #158.36
        mulx      %r14, %r14, %rax                              #159.36
        movl      %r9d, %edx                                    #160.34
        setb      %bpl                                          #156.34
        adox      %r9d, %edx                                    #160.34
        movl      %r9d, %edx                                    #162.34
        adox      %rcx, %r13                                    #160.34
        movl      $0, %ecx                                      #161.34
        adox      %rcx, %r12                                    #161.34
        adox      %rcx, %r14                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %rax, %rdx                                    #163.31
        movl      %r9d, %eax                                    #164.31
        adox      %r9d, %eax                                    #164.31
        adox      %r15, %r8                                     #164.31
        movl      %r9d, %r8d                                    #168.34
        adox      %r13, %r11                                    #165.34
        adox      %r12, %r10                                    #166.34
        movq      %r10, %rax                                    #171.34
        adox      %r14, %rdi                                    #167.34
        movq      %rdi, %r14                                    #172.34
        adox      %rdx, %rbx                                    #168.34
        movq      %r11, %rdx                                    #170.34
        movq      %rbx, %r13                                    #173.34
        seto      %r8b                                          #168.34
        xorl      %r12d, %r12d                                  #168.34
        addl      %r8d, %ebp                                    #174.31
        subq      %rsi, %rdx                                    #170.34
        movq      $0x0ffffffff, %rsi                            #171.34
        movq      $0xffffffff00000001, %r8                      #173.34
        sbbq      %rsi, %rax                                    #171.34
        sbbq      %rcx, %r14                                    #172.34
        sbbq      %r8, %r13                                     #173.34
        setb      %r12b                                         #173.34
        cmpl      %r12d, %r9d                                   #174.31
        sbbq      %rcx, %rbp                                    #174.31
        setb      %r9b                                          #174.31
        testq     %r9, %r9                                      #18.0
        cmovnz    %rbx, %r13                                    #18.0
        movq      %r13, 216(%rsp)                               #18.0[spill]
        testq     %r9, %r9                                      #18.0
        cmovnz    %rdi, %r14                                    #18.0
        movq      %r14, 224(%rsp)                               #18.0[spill]
        testq     %r9, %r9                                      #18.0
        cmovnz    %r10, %rax                                    #18.0
        testq     %r9, %r9                                      #18.0
        cmovnz    %r11, %rdx                                    #18.0
        movq      %r13, (%rsp)                                  #206.37
        movq      %r14, 8(%rsp)                                 #206.37
        movq      %rax, 16(%rsp)                                #206.37
        movq      %rdx, 24(%rsp)                                #206.37
        vmovups   %xmm0, 32(%rsp)                               #208.20
        vmovups   %xmm0, 48(%rsp)                               #208.20
        movq      168(%rsp), %rcx                               #26.23[spill]
        orq       88(%rsp), %rcx                                #26.23[spill]
        orq       176(%rsp), %rcx                               #27.23[spill]
        orq       184(%rsp), %rcx                               #28.23[spill]
        movq      %rcx, 96(%rsp)                                #28.23[spill]
        movq      104(%rsp), %rsi                               #208.66[spill]
        movq      $-1, %r14                                     #80.34
        movq      %rdx, 72(%rsp)                                #[spill]
        movq      %rax, 64(%rsp)                                #[spill]
        vpxor     %xmm0, %xmm0, %xmm0                           #210.21
        movq      (%rsi), %rcx                                  #208.66
        movq      8(%rsi), %rbx                                 #208.73
        movq      16(%rsi), %rbp                                #208.80
        movq      24(%rsi), %r10                                #208.87
        xorl      %esi, %esi                                    #76.32
        mulx      %r10, %r9, %r11                               #72.34
        mulx      %rbp, %r15, %r8                               #73.34
        adcx      %r15, %r11                                    #76.32
        movq      $0x0ffffffff, %r15                            #81.34
        movq      %rbp, 208(%rsp)                               #208.80[spill]
        mulx      %rbx, %rbp, %rdi                              #74.34
        adcx      %rbp, %r8                                     #77.32
        movl      $0, %ebp                                      #78.32
        movq      %rcx, 192(%rsp)                               #208.66[spill]
        mulx      %rcx, %r12, %rcx                              #75.34
        movq      %r9, %rdx                                     #80.34
        adcx      %r12, %rdi                                    #78.32
        movq      %rbx, 200(%rsp)                               #208.73[spill]
        movl      %ebp, %ebx                                    #79.30
        setb      %sil                                          #78.32
        adox      %ebp, %ebx                                    #79.30
        adox      %rcx, %rsi                                    #79.30
        movq      $0xffffffff00000001, %rcx                     #82.34
        mulx      %r14, %r13, %r14                              #80.34
        clc                                                     #83.32
        mulx      %r15, %rbx, %r12                              #81.34
        adcx      %rbx, %r14                                    #83.32
        movl      $0, %ebx                                      #84.32
        mulx      %rcx, %r15, %rcx                              #82.34
        movl      %ebp, %edx                                    #86.30
        adcx      %rbx, %r12                                    #84.32
        movq      %r10, 128(%rsp)                               #208.87[spill]
        adcx      %rbx, %r15                                    #85.32
        movl      %ebp, %ebx                                    #85.32
        setb      %bl                                           #85.32
        adox      %ebp, %edx                                    #86.30
        movq      %rax, %rdx                                    #92.34
        adox      %rcx, %rbx                                    #86.30
        movl      %ebp, %ecx                                    #86.30
        seto      %cl                                           #86.30
        clc                                                     #87.30
        adcx      %r13, %r9                                     #87.30
        movl      %ebp, %r13d                                   #96.32
        adcx      %r14, %r11                                    #88.32
        mulx      %r10, %r14, %rcx                              #92.34
        adcx      %r12, %r8                                     #89.32
        mulx      200(%rsp), %r12, %r9                          #94.34[spill]
        adcx      %r15, %rdi                                    #90.32
        mulx      208(%rsp), %r15, %r10                         #93.34[spill]
        adcx      %rbx, %rsi                                    #91.32
        movl      %ebp, %ebx                                    #91.32
        mulx      192(%rsp), %rdx, %rax                         #95.34[spill]
        setb      %bl                                           #91.32
        adox      %ebp, %r13d                                   #96.32
        movq      $0xffffffff00000001, %r13                     #107.36
        adox      %r15, %rcx                                    #96.32
        movl      %ebp, %r15d                                   #98.32
        adox      %r12, %r10                                    #97.32
        movl      %ebp, %r12d                                   #100.34
        adox      %rdx, %r9                                     #98.32
        seto      %r15b                                         #98.32
        clc                                                     #99.30
        adcx      %rax, %r15                                    #99.30
        adox      %ebp, %r12d                                   #100.34
        movl      %ebp, %eax                                    #104.34
        movl      $0, %r12d                                     #109.34
        adox      %r14, %r11                                    #100.34
        movq      %r11, %rdx                                    #105.36
        adox      %rcx, %r8                                     #101.34
        movq      $0x0ffffffff, %rcx                            #106.36
        adox      %r10, %rdi                                    #102.34
        movq      $-1, %r10                                     #105.36
        adox      %r9, %rsi                                     #103.34
        mulx      %r10, %r10, %r9                               #105.36
        adox      %r15, %rbx                                    #104.34
        mulx      %rcx, %r14, %r15                              #106.36
        seto      %al                                           #104.34
        clc                                                     #108.34
        mulx      %r13, %r13, %rcx                              #107.36
        adcx      %r14, %r9                                     #108.34
        movl      %ebp, %r14d                                   #111.31
        movq      224(%rsp), %rdx                               #118.36[spill]
        adcx      %r12, %r15                                    #109.34
        adcx      %r12, %r13                                    #110.34
        movl      %ebp, %r12d                                   #110.34
        setb      %r12b                                         #110.34
        adox      %ebp, %r14d                                   #111.31
        adox      %rcx, %r12                                    #111.31
        clc                                                     #112.31
        mulx      208(%rsp), %rcx, %r14                         #119.36[spill]
        adcx      %r10, %r11                                    #112.31
        mulx      200(%rsp), %r10, %r11                         #120.36[spill]
        adcx      %r9, %r8                                      #113.34
        movl      %ebp, %r9d                                    #116.34
        adcx      %r15, %rdi                                    #114.34
        adcx      %r13, %rsi                                    #115.34
        movl      %ebp, %r13d                                   #122.34
        adcx      %r12, %rbx                                    #116.34
        setb      %r9b                                          #116.34
        adox      %ebp, %r13d                                   #122.34
        movl      %r9d, 80(%rsp)                                #116.34[spill]
        mulx      128(%rsp), %r12, %r9                          #118.36[spill]
        adox      %rcx, %r9                                     #122.34
        movl      %ebp, %ecx                                    #124.34
        mulx      192(%rsp), %rdx, %r15                         #121.36[spill]
        adox      %r10, %r14                                    #123.34
        movl      %ebp, %r10d                                   #126.34
        adox      %rdx, %r11                                    #124.34
        seto      %cl                                           #124.34
        clc                                                     #125.31
        adcx      %r15, %rcx                                    #125.31
        adox      %ebp, %r10d                                   #126.34
        movq      $0x0ffffffff, %r10                            #132.36
        adox      %r12, %r8                                     #126.34
        movq      %r8, %rdx                                     #131.36
        adox      %r9, %rdi                                     #127.34
        mulx      %r10, %r9, %r12                               #132.36
        adox      %r14, %rsi                                    #128.34
        adox      %r11, %rbx                                    #129.34
        movl      %ebp, %r11d                                   #129.34
        seto      %r11b                                         #129.34
        xorl      %r15d, %r15d                                  #129.34
        addl      80(%rsp), %eax                                #130.34[spill]
        cmpl      %r11d, %ebp                                   #130.34
        movq      $0xffffffff00000001, %r11                     #133.36
        adcx      %rcx, %rax                                    #130.34
        movq      $-1, %rcx                                     #131.36
        mulx      %rcx, %r14, %r13                              #131.36
        mulx      %r11, %r10, %r11                              #133.36
        movl      %ebp, %edx                                    #134.34
        setb      %r15b                                         #130.34
        adox      %ebp, %edx                                    #134.34
        movq      216(%rsp), %rdx                               #144.36[spill]
        adox      %r9, %r13                                     #134.34
        movl      $0, %r9d                                      #135.34
        adox      %r9, %r12                                     #135.34
        adox      %r9, %r10                                     #136.34
        movl      %ebp, %r9d                                    #136.34
        seto      %r9b                                          #136.34
        clc                                                     #137.31
        adcx      %r11, %r9                                     #137.31
        movl      %ebp, %r11d                                   #138.31
        adox      %ebp, %r11d                                   #138.31
        adox      %r14, %r8                                     #138.31
        adox      %r13, %rdi                                    #139.34
        mulx      128(%rsp), %r13, %r11                         #144.36[spill]
        adox      %r12, %rsi                                    #140.34
        mulx      208(%rsp), %r12, %r8                          #145.36[spill]
        adox      %r10, %rbx                                    #141.34
        movl      %ebp, %r10d                                   #142.34
        adox      %r9, %rax                                     #142.34
        seto      %r10b                                         #142.34
        clc                                                     #148.34
        adcx      %r12, %r11                                    #148.34
        mulx      200(%rsp), %r14, %r12                         #146.36[spill]
        adcx      %r14, %r8                                     #149.34
        mulx      192(%rsp), %r9, %r14                          #147.36[spill]
        movl      %ebp, %edx                                    #151.31
        adcx      %r9, %r12                                     #150.34
        movl      %ebp, %r9d                                    #150.34
        setb      %r9b                                          #150.34
        adox      %ebp, %edx                                    #151.31
        adox      %r14, %r9                                     #151.31
        clc                                                     #152.34
        adcx      %r13, %rdi                                    #152.34
        movq      $0xffffffff00000001, %r13                     #159.36
        movq      %rdi, %rdx                                    #157.36
        adcx      %r11, %rsi                                    #153.34
        adcx      %r8, %rbx                                     #154.34
        movl      %ebp, %r8d                                    #155.34
        adcx      %r12, %rax                                    #155.34
        mulx      %rcx, %r14, %r12                              #157.36
        setb      %r8b                                          #155.34
        addl      %r10d, %r15d                                  #156.34
        cmpl      %r8d, %ebp                                    #156.34
        movq      $0x0ffffffff, %r10                            #158.36
        mulx      %r10, %r10, %r11                              #158.36
        adcx      %r9, %r15                                     #156.34
        movl      %ebp, %r9d                                    #156.34
        mulx      %r13, %r13, %r8                               #159.36
        movl      %ebp, %edx                                    #160.34
        setb      %r9b                                          #156.34
        adox      %ebp, %edx                                    #160.34
        movl      %ebp, %edx                                    #162.34
        adox      %r10, %r12                                    #160.34
        movl      $0, %r10d                                     #161.34
        adox      %r10, %r11                                    #161.34
        adox      %r10, %r13                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %r8, %rdx                                     #163.31
        movl      %ebp, %r8d                                    #164.31
        adox      %ebp, %r8d                                    #164.31
        adox      %r14, %rdi                                    #164.31
        movl      %ebp, %edi                                    #168.34
        adox      %r12, %rsi                                    #165.34
        movq      $0xffffffff00000001, %r12                     #173.34
        adox      %r11, %rbx                                    #166.34
        movq      $0x0ffffffff, %r11                            #171.34
        adox      %r13, %rax                                    #167.34
        movq      %rax, %r8                                     #172.34
        adox      %rdx, %r15                                    #168.34
        movq      %r15, %rdx                                    #173.34
        seto      %dil                                          #168.34
        xorl      %r14d, %r14d                                  #168.34
        addl      %edi, %r9d                                    #174.31
        movq      %rsi, %rdi                                    #170.34
        subq      %rcx, %rdi                                    #170.34
        movq      %rbx, %rcx                                    #171.34
        sbbq      %r11, %rcx                                    #171.34
        sbbq      %r10, %r8                                     #172.34
        sbbq      %r12, %rdx                                    #173.34
        setb      %r14b                                         #173.34
        cmpl      %r14d, %ebp                                   #174.31
        sbbq      %r10, %r9                                     #174.31
        setb      %bpl                                          #174.31
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %r15, %rdx                                    #18.0
        movq      %rdx, 144(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rax, %r8                                     #18.0
        movq      %r8, 152(%rsp)                                #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rbx, %rcx                                    #18.0
        movq      %rcx, 160(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rsi, %rdi                                    #18.0
        movq      %rdi, 136(%rsp)                               #18.0[spill]
        movq      %rdx, 32(%rsp)                                #208.34
        movq      %r8, 40(%rsp)                                 #208.34
        movq      %rcx, 48(%rsp)                                #208.34
        movq      %rdi, 56(%rsp)                                #208.34
        vmovups   %xmm0, (%rsp)                                 #210.21
        vmovups   %xmm0, 16(%rsp)                               #210.21
        movq      72(%rsp), %rdx                                #210.21[spill]
        movq      64(%rsp), %rax                                #210.21[spill]
        movq      184(%rsp), %r12                               #72.34[spill]
        xorl      %r8d, %r8d                                    #76.32
        movq      $-1, %r15                                     #76.32
        xorl      %r9d, %r9d                                    #76.32
        mulx      176(%rsp), %rsi, %rdi                         #73.34[spill]
        mulx      %r12, %r11, %r13                              #72.34
        adcx      %rsi, %r13                                    #76.32
        movl      %r8d, %esi                                    #79.30
        vpxor     %xmm0, %xmm0, %xmm0                           #211.19
        mulx      168(%rsp), %rbx, %r10                         #74.34[spill]
        adcx      %rbx, %rdi                                    #77.32
        movq      $0x0ffffffff, %rbx                            #81.34
        mulx      88(%rsp), %rcx, %rbp                          #75.34[spill]
        movq      %r11, %rdx                                    #80.34
        adcx      %rcx, %r10                                    #78.32
        movq      $0xffffffff00000001, %rcx                     #82.34
        mulx      %r15, %r14, %r15                              #80.34
        setb      %r9b                                          #78.32
        adox      %r8d, %esi                                    #79.30
        adox      %rbp, %r9                                     #79.30
        clc                                                     #83.32
        mulx      %rbx, %rsi, %rbp                              #81.34
        adcx      %rsi, %r15                                    #83.32
        movl      $0, %esi                                      #84.32
        mulx      %rcx, %rcx, %rbx                              #82.34
        movl      %r8d, %edx                                    #86.30
        adcx      %rsi, %rbp                                    #84.32
        adcx      %rsi, %rcx                                    #85.32
        movl      %r8d, %esi                                    #85.32
        setb      %sil                                          #85.32
        adox      %r8d, %edx                                    #86.30
        movq      %rax, %rdx                                    #92.34
        adox      %rbx, %rsi                                    #86.30
        movl      %r8d, %ebx                                    #86.30
        movl      %r8d, %eax                                    #96.32
        seto      %bl                                           #86.30
        clc                                                     #87.30
        adcx      %r14, %r11                                    #87.30
        mulx      168(%rsp), %r11, %r14                         #94.34[spill]
        adcx      %r15, %r13                                    #88.32
        adcx      %rbp, %rdi                                    #89.32
        adcx      %rcx, %r10                                    #90.32
        mulx      %r12, %r15, %rcx                              #92.34
        adcx      %rsi, %r9                                     #91.32
        movl      %r8d, %esi                                    #91.32
        mulx      176(%rsp), %rbp, %r12                         #93.34[spill]
        setb      %sil                                          #91.32
        adox      %r8d, %eax                                    #96.32
        mulx      88(%rsp), %rdx, %rbx                          #95.34[spill]
        adox      %rbp, %rcx                                    #96.32
        movl      %r8d, %ebp                                    #98.32
        adox      %r11, %r12                                    #97.32
        movl      %r8d, %r11d                                   #100.34
        adox      %rdx, %r14                                    #98.32
        seto      %bpl                                          #98.32
        clc                                                     #99.30
        adcx      %rbx, %rbp                                    #99.30
        adox      %r8d, %r11d                                   #100.34
        movl      %r8d, %ebx                                    #104.34
        adox      %r15, %r13                                    #100.34
        movq      %r13, %rdx                                    #105.36
        adox      %rcx, %rdi                                    #101.34
        movq      $0x0ffffffff, %rcx                            #106.36
        adox      %r12, %r10                                    #102.34
        movq      $-1, %r12                                     #105.36
        mulx      %r12, %r11, %rax                              #105.36
        movq      $0xffffffff00000001, %r12                     #107.36
        adox      %r14, %r9                                     #103.34
        adox      %rbp, %rsi                                    #104.34
        mulx      %rcx, %r15, %rbp                              #106.36
        seto      %bl                                           #104.34
        clc                                                     #108.34
        mulx      %r12, %r14, %rcx                              #107.36
        movl      %r8d, %r12d                                   #111.31
        adcx      %r15, %rax                                    #108.34
        movl      $0, %r15d                                     #109.34
        movq      224(%rsp), %rdx                               #118.36[spill]
        adcx      %r15, %rbp                                    #109.34
        adcx      %r15, %r14                                    #110.34
        movl      %r8d, %r15d                                   #110.34
        setb      %r15b                                         #110.34
        adox      %r8d, %r12d                                   #111.31
        adox      %rcx, %r15                                    #111.31
        clc                                                     #112.31
        adcx      %r11, %r13                                    #112.31
        movl      %r8d, %r13d                                   #116.34
        adcx      %rax, %rdi                                    #113.34
        mulx      168(%rsp), %r11, %r12                         #120.36[spill]
        adcx      %rbp, %r10                                    #114.34
        adcx      %r14, %r9                                     #115.34
        movl      %r8d, %r14d                                   #122.34
        adcx      %r15, %rsi                                    #116.34
        mulx      176(%rsp), %rcx, %r15                         #119.36[spill]
        setb      %r13b                                         #116.34
        adox      %r8d, %r14d                                   #122.34
        movl      %r13d, 232(%rsp)                              #116.34[spill]
        mulx      184(%rsp), %r13, %rax                         #118.36[spill]
        adox      %rcx, %rax                                    #122.34
        movl      %r8d, %ecx                                    #124.34
        mulx      88(%rsp), %rdx, %rbp                          #121.36[spill]
        adox      %r11, %r15                                    #123.34
        movl      %r8d, %r11d                                   #126.34
        adox      %rdx, %r12                                    #124.34
        seto      %cl                                           #124.34
        clc                                                     #125.31
        adcx      %rbp, %rcx                                    #125.31
        adox      %r8d, %r11d                                   #126.34
        movq      $0xffffffff00000001, %r11                     #133.36
        adox      %r13, %rdi                                    #126.34
        movq      $0x0ffffffff, %r13                            #132.36
        movq      %rdi, %rdx                                    #131.36
        adox      %rax, %r10                                    #127.34
        movl      %r8d, %eax                                    #129.34
        mulx      %r13, %r13, %r14                              #132.36
        adox      %r15, %r9                                     #128.34
        adox      %r12, %rsi                                    #129.34
        mulx      %r11, %r11, %r12                              #133.36
        seto      %al                                           #129.34
        movq      $-1, %rbp                                     #129.34
        addl      232(%rsp), %ebx                               #130.34[spill]
        cmpl      %eax, %r8d                                    #130.34
        mulx      %rbp, %rax, %r15                              #131.36
        movl      %r8d, %edx                                    #134.34
        adcx      %rcx, %rbx                                    #130.34
        movl      %r8d, %ecx                                    #130.34
        setb      %cl                                           #130.34
        adox      %r8d, %edx                                    #134.34
        movq      216(%rsp), %rdx                               #144.36[spill]
        adox      %r13, %r15                                    #134.34
        movl      $0, %r13d                                     #135.34
        adox      %r13, %r14                                    #135.34
        adox      %r13, %r11                                    #136.34
        movl      %r8d, %r13d                                   #136.34
        seto      %r13b                                         #136.34
        clc                                                     #137.31
        adcx      %r12, %r13                                    #137.31
        movl      %r8d, %r12d                                   #138.31
        adox      %r8d, %r12d                                   #138.31
        adox      %rax, %rdi                                    #138.31
        adox      %r15, %r10                                    #139.34
        mulx      176(%rsp), %r15, %rdi                         #145.36[spill]
        adox      %r14, %r9                                     #140.34
        mulx      184(%rsp), %r14, %r12                         #144.36[spill]
        adox      %r11, %rsi                                    #141.34
        movl      %r8d, %r11d                                   #142.34
        adox      %r13, %rbx                                    #142.34
        mulx      168(%rsp), %rax, %r13                         #146.36[spill]
        seto      %r11b                                         #142.34
        clc                                                     #148.34
        adcx      %r15, %r12                                    #148.34
        adcx      %rax, %rdi                                    #149.34
        mulx      88(%rsp), %rax, %r15                          #147.36[spill]
        movl      %r8d, %edx                                    #151.31
        adcx      %rax, %r13                                    #150.34
        movl      %r8d, %eax                                    #150.34
        setb      %al                                           #150.34
        adox      %r8d, %edx                                    #151.31
        adox      %r15, %rax                                    #151.31
        clc                                                     #152.34
        adcx      %r14, %r10                                    #152.34
        movq      $0xffffffff00000001, %r14                     #159.36
        movq      %r10, %rdx                                    #157.36
        adcx      %r12, %r9                                     #153.34
        adcx      %rdi, %rsi                                    #154.34
        movl      %r8d, %edi                                    #155.34
        adcx      %r13, %rbx                                    #155.34
        mulx      %rbp, %r15, %r13                              #157.36
        setb      %dil                                          #155.34
        addl      %r11d, %ecx                                   #156.34
        cmpl      %edi, %r8d                                    #156.34
        movq      $0x0ffffffff, %r11                            #158.36
        mulx      %r11, %r11, %r12                              #158.36
        adcx      %rax, %rcx                                    #156.34
        movl      %r8d, %eax                                    #156.34
        mulx      %r14, %r14, %rdi                              #159.36
        movl      %r8d, %edx                                    #160.34
        setb      %al                                           #156.34
        adox      %r8d, %edx                                    #160.34
        movl      %r8d, %edx                                    #162.34
        adox      %r11, %r13                                    #160.34
        movl      $0, %r11d                                     #161.34
        adox      %r11, %r12                                    #161.34
        adox      %r11, %r14                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %rdi, %rdx                                    #163.31
        movl      %r8d, %edi                                    #164.31
        adox      %r8d, %edi                                    #164.31
        movq      $0x0ffffffff, %rdi                            #171.34
        adox      %r15, %r10                                    #164.31
        movl      %r8d, %r10d                                   #168.34
        adox      %r13, %r9                                     #165.34
        adox      %r12, %rsi                                    #166.34
        adox      %r14, %rbx                                    #167.34
        movq      %rbx, %r14                                    #172.34
        adox      %rdx, %rcx                                    #168.34
        movq      %r9, %rdx                                     #170.34
        movq      %rcx, %r13                                    #173.34
        seto      %r10b                                         #168.34
        xorl      %r12d, %r12d                                  #168.34
        addl      %r10d, %eax                                   #174.31
        subq      %rbp, %rdx                                    #170.34
        movq      %rsi, %rbp                                    #171.34
        movq      $0xffffffff00000001, %r10                     #173.34
        sbbq      %rdi, %rbp                                    #171.34
        sbbq      %r11, %r14                                    #172.34
        sbbq      %r10, %r13                                    #173.34
        setb      %r12b                                         #173.34
        cmpl      %r12d, %r8d                                   #174.31
        sbbq      %r11, %rax                                    #174.31
        setb      %r8b                                          #174.31
        testq     %r8, %r8                                      #18.0
        cmovnz    %rcx, %r13                                    #18.0
        movq      %r13, 64(%rsp)                                #18.0[spill]
        testq     %r8, %r8                                      #18.0
        cmovnz    %rbx, %r14                                    #18.0
        movq      %r14, 72(%rsp)                                #18.0[spill]
        testq     %r8, %r8                                      #18.0
        cmovnz    %rsi, %rbp                                    #18.0
        movq      %rbp, 80(%rsp)                                #18.0[spill]
        testq     %r8, %r8                                      #18.0
        cmovnz    %r9, %rdx                                     #18.0
        movq      %r13, (%rsp)                                  #210.35
        movq      %r14, 8(%rsp)                                 #210.35
        movq      %rbp, 16(%rsp)                                #210.35
        movq      %rdx, 24(%rsp)                                #210.35
        vmovups   %xmm0, 32(%rsp)                               #211.19
        vmovups   %xmm0, 48(%rsp)                               #211.19
        movq      120(%rsp), %rax                               #53.32[spill]
        xorl      %r13d, %r13d                                  #18.0
        movq      200(%rsp), %r9                                #26.23[spill]
        orq       192(%rsp), %r9                                #26.23[spill]
        vpxor     %xmm0, %xmm0, %xmm0                           #215.20
        movq      136(%rsp), %rdi                               #53.32[spill]
        movq      208(%rsp), %rbp                               #27.23[spill]
        orq       %r9, %rbp                                     #27.23
        xorl      %r9d, %r9d                                    #53.32
        xorl      %r11d, %r11d                                  #53.32
        subq      24(%rax), %rdi                                #53.32
        movq      160(%rsp), %r10                               #54.32[spill]
        sbbq      16(%rax), %r10                                #54.32
        movq      152(%rsp), %rsi                               #55.32[spill]
        sbbq      8(%rax), %rsi                                 #55.32
        movq      144(%rsp), %r12                               #56.32[spill]
        sbbq      (%rax), %r12                                  #56.32
        movq      %rdx, 240(%rsp)                               #[spill]
        setb      %r11b                                         #56.32
        xorl      %r15d, %r15d                                  #56.32
        xorl      %ebx, %ebx                                    #56.32
        xorl      %r14d, %r14d                                  #56.32
        movq      $-1, %rdx                                     #56.32
        orq       %rbp, 128(%rsp)                               #28.23[spill]
        xorl      %ebp, %ebp                                    #62.32
        testq     %r11, %r11                                    #18.0
        cmovnz    %rdx, %r13                                    #18.0
        xorl      %r8d, %r8d                                    #59.32
        movl      %r13d, %ecx                                   #61.32
        movq      $0xffffffff00000001, %r11                     #64.30
        adcx      %r13, %rdi                                    #59.32
        movq      184(%rsp), %rdx                               #72.34[spill]
        adcx      %rcx, %r10                                    #61.32
        movq      %r10, 160(%rsp)                               #61.32[spill]
        adcx      %rbp, %rsi                                    #62.32
        movq      %r10, 48(%rsp)                                #211.33
        setb      %r15b                                         #62.32
        andq      %r11, %r13                                    #64.30
        cmpl      %r15d, %r9d                                   #64.30
        mulx      %r10, %rax, %r10                              #73.34
        adcx      %r13, %r12                                    #64.30
        movq      $-1, %r13                                     #80.34
        movq      %rsi, 152(%rsp)                               #62.32[spill]
        setb      %bl                                           #64.30
        adox      %r9d, %r14d                                   #76.32
        mulx      %rdi, %rcx, %rbx                              #72.34
        adox      %rax, %rbx                                    #76.32
        movq      %rsi, 40(%rsp)                                #211.33
        mulx      %rsi, %r8, %rsi                               #74.34
        adox      %r8, %r10                                     #77.32
        movl      %r9d, %r8d                                    #78.32
        movq      %r12, 144(%rsp)                               #64.30[spill]
        movq      %r12, 32(%rsp)                                #211.33
        mulx      %r12, %r12, %r15                              #75.34
        movq      %rcx, %rdx                                    #80.34
        adox      %r12, %rsi                                    #78.32
        mulx      %r13, %r13, %r14                              #80.34
        seto      %r8b                                          #78.32
        clc                                                     #79.30
        adcx      %r15, %r8                                     #79.30
        movq      %rdi, 136(%rsp)                               #59.32[spill]
        movq      $0x0ffffffff, %rax                            #81.34
        mulx      %rax, %r12, %r15                              #81.34
        movl      %r9d, %eax                                    #83.32
        adox      %r9d, %eax                                    #83.32
        mulx      %r11, %r11, %rdx                              #82.34
        movl      %r9d, %eax                                    #85.32
        adox      %r12, %r14                                    #83.32
        movq      %rdi, 56(%rsp)                                #211.33
        adox      %rbp, %r15                                    #84.32
        adox      %rbp, %r11                                    #85.32
        seto      %al                                           #85.32
        clc                                                     #86.30
        adcx      %rdx, %rax                                    #86.30
        movq      176(%rsp), %rdx                               #92.34[spill]
        movl      %r9d, %r12d                                   #87.30
        adox      %r9d, %r12d                                   #87.30
        adox      %r13, %rcx                                    #87.30
        movl      %r9d, %ecx                                    #91.32
        adox      %r14, %rbx                                    #88.32
        adox      %r15, %r10                                    #89.32
        mulx      %rdi, %r15, %r13                              #92.34
        adox      %r11, %rsi                                    #90.32
        mulx      160(%rsp), %r11, %r14                         #93.34[spill]
        adox      %rax, %r8                                     #91.32
        mulx      152(%rsp), %rax, %r12                         #94.34[spill]
        seto      %cl                                           #91.32
        clc                                                     #96.32
        adcx      %r11, %r13                                    #96.32
        adcx      %rax, %r14                                    #97.32
        mulx      144(%rsp), %rax, %r11                         #95.34[spill]
        movl      %r9d, %edx                                    #99.30
        adcx      %rax, %r12                                    #98.32
        movl      %r9d, %eax                                    #98.32
        setb      %al                                           #98.32
        adox      %r9d, %edx                                    #99.30
        adox      %r11, %rax                                    #99.30
        clc                                                     #100.34
        adcx      %r15, %rbx                                    #100.34
        movq      $0x0ffffffff, %r15                            #106.36
        movq      %rbx, %rdx                                    #105.36
        adcx      %r13, %r10                                    #101.34
        adcx      %r14, %rsi                                    #102.34
        movq      $-1, %r14                                     #105.36
        mulx      %r14, %r14, %r13                              #105.36
        adcx      %r12, %r8                                     #103.34
        movl      %r9d, %r12d                                   #104.34
        adcx      %rax, %rcx                                    #104.34
        mulx      %r15, %r11, %rax                              #106.36
        setb      %r12b                                         #104.34
        movl      %r12d, 248(%rsp)                              #104.34[spill]
        movq      $0xffffffff00000001, %r12                     #107.36
        mulx      %r12, %r12, %r15                              #107.36
        movl      %r9d, %edx                                    #108.34
        adox      %r9d, %edx                                    #108.34
        movq      168(%rsp), %rdx                               #118.36[spill]
        adox      %r11, %r13                                    #108.34
        movl      %r9d, %r11d                                   #110.34
        adox      %rbp, %rax                                    #109.34
        adox      %rbp, %r12                                    #110.34
        seto      %r11b                                         #110.34
        clc                                                     #111.31
        adcx      %r15, %r11                                    #111.31
        movl      %r9d, %r15d                                   #112.31
        adox      %r9d, %r15d                                   #112.31
        adox      %r14, %rbx                                    #112.31
        movl      %r9d, %r14d                                   #116.34
        adox      %r13, %r10                                    #113.34
        adox      %rax, %rsi                                    #114.34
        mulx      160(%rsp), %rax, %rbx                         #119.36[spill]
        adox      %r12, %r8                                     #115.34
        mulx      %rdi, %r13, %r12                              #118.36
        adox      %r11, %rcx                                    #116.34
        seto      %r14b                                         #116.34
        clc                                                     #122.34
        adcx      %rax, %r12                                    #122.34
        mulx      152(%rsp), %rax, %r11                         #120.36[spill]
        adcx      %rax, %rbx                                    #123.34
        mulx      144(%rsp), %r15, %rax                         #121.36[spill]
        movl      %r9d, %edx                                    #125.31
        adcx      %r15, %r11                                    #124.34
        movl      %r9d, %r15d                                   #124.34
        setb      %r15b                                         #124.34
        adox      %r9d, %edx                                    #125.31
        adox      %rax, %r15                                    #125.31
        clc                                                     #126.34
        movl      248(%rsp), %eax                               #130.34[spill]
        adcx      %r13, %r10                                    #126.34
        movl      %r9d, %r13d                                   #129.34
        movq      %r10, %rdx                                    #131.36
        adcx      %r12, %rsi                                    #127.34
        adcx      %rbx, %r8                                     #128.34
        adcx      %r11, %rcx                                    #129.34
        setb      %r13b                                         #129.34
        xorl      %ebx, %ebx                                    #129.34
        movq      $-1, %r11                                     #129.34
        addl      %r14d, %eax                                   #130.34
        cmpl      %r13d, %r9d                                   #130.34
        movq      $0x0ffffffff, %r13                            #132.36
        movq      $0xffffffff00000001, %r14                     #133.36
        adcx      %r15, %rax                                    #130.34
        mulx      %r11, %r15, %r12                              #131.36
        setb      %bl                                           #130.34
        movl      %ebx, 256(%rsp)                               #130.34[spill]
        mulx      %r13, %r11, %rbx                              #132.36
        mulx      %r14, %r13, %r14                              #133.36
        movl      %r9d, %edx                                    #134.34
        adox      %r9d, %edx                                    #134.34
        movq      88(%rsp), %rdx                                #144.36[spill]
        adox      %r11, %r12                                    #134.34
        movl      %r9d, %r11d                                   #136.34
        adox      %rbp, %rbx                                    #135.34
        adox      %rbp, %r13                                    #136.34
        seto      %r11b                                         #136.34
        clc                                                     #137.31
        adcx      %r14, %r11                                    #137.31
        movl      %r9d, %r14d                                   #138.31
        adox      %r9d, %r14d                                   #138.31
        movl      %r9d, %r14d                                   #151.31
        adox      %r15, %r10                                    #138.31
        adox      %r12, %rsi                                    #139.34
        adox      %rbx, %r8                                     #140.34
        movl      %r9d, %ebx                                    #142.34
        adox      %r13, %rcx                                    #141.34
        mulx      %rdi, %r10, %r13                              #144.36
        adox      %r11, %rax                                    #142.34
        mulx      160(%rsp), %rdi, %r11                         #145.36[spill]
        seto      %bl                                           #142.34
        clc                                                     #148.34
        adcx      %rdi, %r13                                    #148.34
        mulx      152(%rsp), %r12, %rdi                         #146.36[spill]
        adcx      %r12, %r11                                    #149.34
        mulx      144(%rsp), %r15, %r12                         #147.36[spill]
        adcx      %r15, %rdi                                    #150.34
        movl      %r9d, %r15d                                   #150.34
        setb      %r15b                                         #150.34
        adox      %r9d, %r14d                                   #151.31
        adox      %r12, %r15                                    #151.31
        clc                                                     #152.34
        movl      256(%rsp), %r12d                              #156.34[spill]
        adcx      %r10, %rsi                                    #152.34
        movq      %rsi, %rdx                                    #157.36
        adcx      %r13, %r8                                     #153.34
        movq      $0xffffffff00000001, %r13                     #159.36
        mulx      %r13, %r13, %r14                              #159.36
        adcx      %r11, %rcx                                    #154.34
        movl      %r9d, %r11d                                   #155.34
        adcx      %rdi, %rax                                    #155.34
        movq      $0x0ffffffff, %rdi                            #158.36
        setb      %r11b                                         #155.34
        movq      $-1, %r10                                     #155.34
        addl      %ebx, %r12d                                   #156.34
        cmpl      %r11d, %r9d                                   #156.34
        mulx      %r10, %r11, %r10                              #157.36
        adcx      %r15, %r12                                    #156.34
        movl      %r9d, %r15d                                   #156.34
        mulx      %rdi, %rbx, %rdi                              #158.36
        movl      %r9d, %edx                                    #160.34
        setb      %r15b                                         #156.34
        adox      %r9d, %edx                                    #160.34
        movq      $0x0ffffffff, %rdx                            #171.34
        adox      %rbx, %r10                                    #160.34
        movl      %r9d, %ebx                                    #162.34
        adox      %rbp, %rdi                                    #161.34
        adox      %rbp, %r13                                    #162.34
        seto      %bl                                           #162.34
        clc                                                     #163.31
        adcx      %r14, %rbx                                    #163.31
        movl      %r9d, %r14d                                   #164.31
        adox      %r9d, %r14d                                   #164.31
        adox      %r11, %rsi                                    #164.31
        movl      %r9d, %r11d                                   #168.34
        adox      %r10, %r8                                     #165.34
        adox      %rdi, %rcx                                    #166.34
        movq      %rcx, %r10                                    #171.34
        adox      %r13, %rax                                    #167.34
        adox      %rbx, %r12                                    #168.34
        movq      $0xffffffff00000001, %rbx                     #173.34
        seto      %r11b                                         #168.34
        movq      $-1, %rsi                                     #168.34
        xorl      %edi, %edi                                    #168.34
        addl      %r11d, %r15d                                  #174.31
        movq      %r8, %r11                                     #170.34
        subq      %rsi, %r11                                    #170.34
        movq      %r12, %rsi                                    #173.34
        sbbq      %rdx, %r10                                    #171.34
        movq      %rax, %rdx                                    #172.34
        sbbq      %rbp, %rdx                                    #172.34
        sbbq      %rbx, %rsi                                    #173.34
        setb      %dil                                          #173.34
        cmpl      %edi, %r9d                                    #174.31
        sbbq      %rbp, %r15                                    #174.31
        setb      %r9b                                          #174.31
        testq     %r9, %r9                                      #18.0
        cmovnz    %r12, %rsi                                    #18.0
        testq     %r9, %r9                                      #18.0
        cmovnz    %rax, %rdx                                    #18.0
        testq     %r9, %r9                                      #18.0
        cmovnz    %rcx, %r10                                    #18.0
        testq     %r9, %r9                                      #18.0
        cmovnz    %r8, %r11                                     #18.0
        movq      112(%rsp), %rbp                               #18.0[spill]
        movq      %rdx, 72(%rbp)                                #180.1
        movq      104(%rsp), %rdx                               #213.58[spill]
        movq      %r11, 88(%rbp)                                #18.0
        movq      %rsi, 64(%rbp)                                #179.1
        movq      %r10, 80(%rbp)                                #181.1
        movq      40(%rdx), %rcx                                #213.44
        movq      32(%rdx), %rbx                                #213.37
        movq      %rcx, 216(%rsp)                               #213.44[spill]
        orq       %rbx, %rcx                                    #26.23
        movq      48(%rdx), %rbp                                #213.51
        orq       %rbp, %rcx                                    #27.23
        movq      56(%rdx), %rax                                #213.58
        orq       %rax, %rcx                                    #28.23
        movq      %rbp, 232(%rsp)                               #213.51[spill]
        movq      %rbx, 224(%rsp)                               #213.37[spill]
        vmovups   %xmm0, (%rsp)                                 #215.20
        vmovups   %xmm0, 16(%rsp)                               #215.20
        orq       %rcx, 128(%rsp)                               #214.28[spill]
        movq      240(%rsp), %rdx                               #214.28[spill]
        movq      %rbp, %r10                                    #73.34
        xorl      %ebp, %ebp                                    #76.32
        movq      $-1, %r14                                     #76.32
        xorl      %esi, %esi                                    #76.32
        mulx      %rax, %r9, %r11                               #72.34
        mulx      %r10, %rbx, %r8                               #73.34
        adcx      %rbx, %r11                                    #76.32
        movl      %ebp, %ebx                                    #79.30
        vpxor     %xmm0, %xmm0, %xmm0                           #216.19
        mulx      216(%rsp), %rcx, %rdi                         #74.34[spill]
        adcx      %rcx, %r8                                     #77.32
        movq      $0x0ffffffff, %rcx                            #81.34
        mulx      224(%rsp), %r15, %r12                         #75.34[spill]
        movq      %r9, %rdx                                     #80.34
        adcx      %r15, %rdi                                    #78.32
        movq      $0xffffffff00000001, %r15                     #82.34
        mulx      %r14, %r13, %r14                              #80.34
        setb      %sil                                          #78.32
        adox      %ebp, %ebx                                    #79.30
        adox      %r12, %rsi                                    #79.30
        movq      %rax, 88(%rsp)                                #[spill]
        clc                                                     #83.32
        mulx      %rcx, %rbx, %r12                              #81.34
        adcx      %rbx, %r14                                    #83.32
        movl      $0, %ebx                                      #84.32
        mulx      %r15, %r15, %rcx                              #82.34
        movl      %ebp, %edx                                    #86.30
        adcx      %rbx, %r12                                    #84.32
        adcx      %rbx, %r15                                    #85.32
        movl      %ebp, %ebx                                    #85.32
        setb      %bl                                           #85.32
        adox      %ebp, %edx                                    #86.30
        adox      %rcx, %rbx                                    #86.30
        movq      80(%rsp), %rdx                                #92.34[spill]
        clc                                                     #87.30
        mulx      %r10, %rcx, %r10                              #93.34
        adcx      %r13, %r9                                     #87.30
        movl      %ebp, %r13d                                   #96.32
        adcx      %r14, %r11                                    #88.32
        adcx      %r12, %r8                                     #89.32
        mulx      %rax, %r14, %r12                              #92.34
        adcx      %r15, %rdi                                    #90.32
        mulx      216(%rsp), %r15, %r9                          #94.34[spill]
        adcx      %rbx, %rsi                                    #91.32
        movl      %ebp, %ebx                                    #91.32
        mulx      224(%rsp), %rdx, %rax                         #95.34[spill]
        setb      %bl                                           #91.32
        adox      %ebp, %r13d                                   #96.32
        movq      $0xffffffff00000001, %r13                     #107.36
        adox      %rcx, %r12                                    #96.32
        movl      %ebp, %ecx                                    #100.34
        adox      %r15, %r10                                    #97.32
        movl      %ebp, %r15d                                   #98.32
        adox      %rdx, %r9                                     #98.32
        seto      %r15b                                         #98.32
        clc                                                     #99.30
        adcx      %rax, %r15                                    #99.30
        adox      %ebp, %ecx                                    #100.34
        movl      %ebp, %eax                                    #104.34
        adox      %r14, %r11                                    #100.34
        movq      %r11, %rdx                                    #105.36
        adox      %r12, %r8                                     #101.34
        movq      $0x0ffffffff, %r12                            #106.36
        mulx      %r13, %r13, %rcx                              #107.36
        adox      %r10, %rdi                                    #102.34
        movq      $-1, %r10                                     #105.36
        adox      %r9, %rsi                                     #103.34
        mulx      %r10, %r10, %r9                               #105.36
        adox      %r15, %rbx                                    #104.34
        mulx      %r12, %r14, %r15                              #106.36
        movl      $0, %r12d                                     #109.34
        seto      %al                                           #104.34
        clc                                                     #108.34
        movq      72(%rsp), %rdx                                #118.36[spill]
        adcx      %r14, %r9                                     #108.34
        movl      %ebp, %r14d                                   #111.31
        adcx      %r12, %r15                                    #109.34
        adcx      %r12, %r13                                    #110.34
        movl      %ebp, %r12d                                   #110.34
        setb      %r12b                                         #110.34
        adox      %ebp, %r14d                                   #111.31
        adox      %rcx, %r12                                    #111.31
        clc                                                     #112.31
        mulx      232(%rsp), %rcx, %r14                         #119.36[spill]
        adcx      %r10, %r11                                    #112.31
        mulx      216(%rsp), %r10, %r11                         #120.36[spill]
        adcx      %r9, %r8                                      #113.34
        movl      %ebp, %r9d                                    #116.34
        adcx      %r15, %rdi                                    #114.34
        adcx      %r13, %rsi                                    #115.34
        movl      %ebp, %r13d                                   #122.34
        adcx      %r12, %rbx                                    #116.34
        setb      %r9b                                          #116.34
        adox      %ebp, %r13d                                   #122.34
        movl      %r9d, 200(%rsp)                               #116.34[spill]
        mulx      88(%rsp), %r12, %r9                           #118.36[spill]
        adox      %rcx, %r9                                     #122.34
        movl      %ebp, %ecx                                    #124.34
        mulx      224(%rsp), %rdx, %r15                         #121.36[spill]
        adox      %r10, %r14                                    #123.34
        movl      %ebp, %r10d                                   #126.34
        adox      %rdx, %r11                                    #124.34
        seto      %cl                                           #124.34
        clc                                                     #125.31
        adcx      %r15, %rcx                                    #125.31
        adox      %ebp, %r10d                                   #126.34
        movq      $0x0ffffffff, %r10                            #132.36
        adox      %r12, %r8                                     #126.34
        movq      %r8, %rdx                                     #131.36
        adox      %r9, %rdi                                     #127.34
        mulx      %r10, %r9, %r12                               #132.36
        adox      %r14, %rsi                                    #128.34
        adox      %r11, %rbx                                    #129.34
        movl      %ebp, %r11d                                   #129.34
        seto      %r11b                                         #129.34
        xorl      %r15d, %r15d                                  #129.34
        addl      200(%rsp), %eax                               #130.34[spill]
        cmpl      %r11d, %ebp                                   #130.34
        movq      $0xffffffff00000001, %r11                     #133.36
        adcx      %rcx, %rax                                    #130.34
        movq      $-1, %rcx                                     #131.36
        mulx      %rcx, %r14, %r13                              #131.36
        mulx      %r11, %r10, %r11                              #133.36
        movl      %ebp, %edx                                    #134.34
        setb      %r15b                                         #130.34
        adox      %ebp, %edx                                    #134.34
        movq      64(%rsp), %rdx                                #144.36[spill]
        adox      %r9, %r13                                     #134.34
        movl      $0, %r9d                                      #135.34
        adox      %r9, %r12                                     #135.34
        adox      %r9, %r10                                     #136.34
        movl      %ebp, %r9d                                    #136.34
        seto      %r9b                                          #136.34
        clc                                                     #137.31
        adcx      %r11, %r9                                     #137.31
        movl      %ebp, %r11d                                   #138.31
        adox      %ebp, %r11d                                   #138.31
        adox      %r14, %r8                                     #138.31
        adox      %r13, %rdi                                    #139.34
        mulx      88(%rsp), %r13, %r11                          #144.36[spill]
        adox      %r12, %rsi                                    #140.34
        mulx      232(%rsp), %r12, %r8                          #145.36[spill]
        adox      %r10, %rbx                                    #141.34
        movl      %ebp, %r10d                                   #142.34
        adox      %r9, %rax                                     #142.34
        seto      %r10b                                         #142.34
        clc                                                     #148.34
        adcx      %r12, %r11                                    #148.34
        mulx      216(%rsp), %r14, %r12                         #146.36[spill]
        adcx      %r14, %r8                                     #149.34
        mulx      224(%rsp), %r9, %r14                          #147.36[spill]
        movl      %ebp, %edx                                    #151.31
        adcx      %r9, %r12                                     #150.34
        movl      %ebp, %r9d                                    #150.34
        setb      %r9b                                          #150.34
        adox      %ebp, %edx                                    #151.31
        adox      %r14, %r9                                     #151.31
        clc                                                     #152.34
        adcx      %r13, %rdi                                    #152.34
        movq      $0xffffffff00000001, %r13                     #159.36
        movq      %rdi, %rdx                                    #157.36
        adcx      %r11, %rsi                                    #153.34
        adcx      %r8, %rbx                                     #154.34
        movl      %ebp, %r8d                                    #155.34
        adcx      %r12, %rax                                    #155.34
        mulx      %rcx, %r14, %r12                              #157.36
        setb      %r8b                                          #155.34
        addl      %r10d, %r15d                                  #156.34
        cmpl      %r8d, %ebp                                    #156.34
        movq      $0x0ffffffff, %r10                            #158.36
        mulx      %r10, %r10, %r11                              #158.36
        adcx      %r9, %r15                                     #156.34
        movl      %ebp, %r9d                                    #156.34
        mulx      %r13, %r13, %r8                               #159.36
        movl      %ebp, %edx                                    #160.34
        setb      %r9b                                          #156.34
        adox      %ebp, %edx                                    #160.34
        movl      %ebp, %edx                                    #162.34
        adox      %r10, %r12                                    #160.34
        movl      $0, %r10d                                     #161.34
        adox      %r10, %r11                                    #161.34
        adox      %r10, %r13                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %r8, %rdx                                     #163.31
        movl      %ebp, %r8d                                    #164.31
        adox      %ebp, %r8d                                    #164.31
        adox      %r14, %rdi                                    #164.31
        movl      %ebp, %edi                                    #168.34
        adox      %r12, %rsi                                    #165.34
        movq      $0xffffffff00000001, %r12                     #173.34
        adox      %r11, %rbx                                    #166.34
        movq      $0x0ffffffff, %r11                            #171.34
        adox      %r13, %rax                                    #167.34
        movq      %rax, %r8                                     #172.34
        adox      %rdx, %r15                                    #168.34
        movq      %r15, %rdx                                    #173.34
        seto      %dil                                          #168.34
        xorl      %r14d, %r14d                                  #168.34
        addl      %edi, %r9d                                    #174.31
        movq      %rsi, %rdi                                    #170.34
        subq      %rcx, %rdi                                    #170.34
        movq      %rbx, %rcx                                    #171.34
        sbbq      %r11, %rcx                                    #171.34
        sbbq      %r10, %r8                                     #172.34
        sbbq      %r12, %rdx                                    #173.34
        setb      %r14b                                         #173.34
        cmpl      %r14d, %ebp                                   #174.31
        sbbq      %r10, %r9                                     #174.31
        setb      %bpl                                          #174.31
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %r15, %rdx                                    #18.0
        movq      %rdx, 192(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rax, %r8                                     #18.0
        movq      %r8, 176(%rsp)                                #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rbx, %rcx                                    #18.0
        movq      %rcx, 184(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rsi, %rdi                                    #18.0
        movq      %rdi, 168(%rsp)                               #18.0[spill]
        movq      %rdx, (%rsp)                                  #215.34
        movq      %r8, 8(%rsp)                                  #215.34
        movq      %rcx, 16(%rsp)                                #215.34
        movq      %rdi, 24(%rsp)                                #215.34
        vmovups   %xmm0, 32(%rsp)                               #216.19
        vmovups   %xmm0, 48(%rsp)                               #216.19
        movq      %rdx, %rax                                    #56.32
        movq      %r8, %r10                                     #55.32
        movq      %rcx, %r8                                     #54.32
        movq      120(%rsp), %rdx                               #53.32[spill]
        xorl      %r14d, %r14d                                  #53.32
        movq      %rdi, %rsi                                    #53.32
        xorl      %ecx, %ecx                                    #56.32
        movq      $-1, %rbx                                     #18.0
        subq      56(%rdx), %rsi                                #53.32
        sbbq      48(%rdx), %r8                                 #54.32
        movq      $0xffffffff00000001, %r13                     #64.30
        sbbq      40(%rdx), %r10                                #55.32
        vpxor     %xmm0, %xmm0, %xmm0                           #217.20
        sbbq      32(%rdx), %rax                                #56.32
        setb      %cl                                           #56.32
        xorl      %r11d, %r11d                                  #56.32
        xorl      %r9d, %r9d                                    #56.32
        xorl      %r12d, %r12d                                  #56.32
        testq     %rcx, %rcx                                    #18.0
        cmovnz    %rbx, %r11                                    #18.0
        xorl      %ebp, %ebp                                    #59.32
        movl      %r11d, %edi                                   #61.32
        adcx      %r11, %rsi                                    #59.32
        movq      %rsi, 168(%rsp)                               #59.32[spill]
        adcx      %rdi, %r8                                     #61.32
        movq      %rsi, 56(%rsp)                                #216.33
        adcx      %r9, %r10                                     #62.32
        movq      %r8, 184(%rsp)                                #61.32[spill]
        setb      %r12b                                         #62.32
        andq      %r11, %r13                                    #64.30
        cmpl      %r12d, %r14d                                  #64.30
        movq      %r8, 48(%rsp)                                 #216.33
        adcx      %r13, %rax                                    #64.30
        movq      %r10, 176(%rsp)                               #62.32[spill]
        movq      %r10, 40(%rsp)                                #216.33
        movq      %rax, 192(%rsp)                               #64.30[spill]
        movq      %rax, 32(%rsp)                                #216.33
        vmovups   %xmm0, 64(%rsp)                               #217.20
        vmovups   %xmm0, 80(%rsp)                               #217.20
        movq      136(%rsp), %rsi                               #72.34[spill]
        movq      %rsi, %rdx                                    #72.34
        movq      160(%rsp), %rdi                               #73.34[spill]
        xorl      %r9d, %r9d                                    #76.32
        movq      $-1, %r15                                     #76.32
        xorl      %ecx, %ecx                                    #76.32
        xorl      %r10d, %r10d                                  #76.32
        mulx      %rsi, %rbx, %r8                               #72.34
        mulx      %rdi, %rbp, %r12                              #73.34
        adox      %rbp, %r8                                     #76.32
        vpxor     %xmm0, %xmm0, %xmm0                           #218.20
        mulx      152(%rsp), %rax, %r11                         #74.34[spill]
        adox      %rax, %r12                                    #77.32
        mulx      144(%rsp), %r14, %r13                         #75.34[spill]
        movq      %rbx, %rdx                                    #80.34
        adox      %r14, %r11                                    #78.32
        movq      $0x0ffffffff, %r14                            #81.34
        mulx      %r15, %rbp, %rax                              #80.34
        movq      $0xffffffff00000001, %r15                     #82.34
        seto      %r10b                                         #78.32
        clc                                                     #79.30
        adcx      %r13, %r10                                    #79.30
        setb      %cl                                           #79.30
        mulx      %r14, %r13, %rcx                              #81.34
        mulx      %r15, %r15, %r14                              #82.34
        movl      %r9d, %edx                                    #83.32
        adox      %r9d, %edx                                    #83.32
        movl      %r9d, %edx                                    #85.32
        adox      %r13, %rax                                    #83.32
        movl      $0, %r13d                                     #84.32
        adox      %r13, %rcx                                    #84.32
        adox      %r13, %r15                                    #85.32
        seto      %dl                                           #85.32
        clc                                                     #86.30
        adcx      %r14, %rdx                                    #86.30
        movl      %r9d, %r14d                                   #87.30
        adox      %r9d, %r14d                                   #87.30
        adox      %rbp, %rbx                                    #87.30
        movl      %r9d, %ebp                                    #91.32
        adox      %rax, %r8                                     #88.32
        adox      %rcx, %r12                                    #89.32
        adox      %r15, %r11                                    #90.32
        adox      %rdx, %r10                                    #91.32
        movq      %rdi, %rdx                                    #92.34
        mulx      %rsi, %rsi, %r14                              #92.34
        seto      %bpl                                          #91.32
        clc                                                     #96.32
        mulx      %rdi, %rbx, %rax                              #93.34
        adcx      %rbx, %r14                                    #96.32
        movq      152(%rsp), %rbx                               #94.34[spill]
        mulx      %rbx, %r15, %rcx                              #94.34
        adcx      %r15, %rax                                    #97.32
        mulx      144(%rsp), %r15, %rdi                         #95.34[spill]
        movl      %r9d, %edx                                    #99.30
        adcx      %r15, %rcx                                    #98.32
        movl      %r9d, %r15d                                   #98.32
        setb      %r15b                                         #98.32
        adox      %r9d, %edx                                    #99.30
        adox      %rdi, %r15                                    #99.30
        movl      %r9d, %edi                                    #99.30
        seto      %dil                                          #99.30
        clc                                                     #100.34
        adcx      %rsi, %r8                                     #100.34
        movl      %r9d, %esi                                    #104.34
        movq      %r8, %rdx                                     #105.36
        adcx      %r14, %r12                                    #101.34
        movq      $0x0ffffffff, %r14                            #106.36
        adcx      %rax, %r11                                    #102.34
        movq      $-1, %rax                                     #105.36
        adcx      %rcx, %r10                                    #103.34
        mulx      %r14, %rcx, %rdi                              #106.36
        adcx      %r15, %rbp                                    #104.34
        mulx      %rax, %r15, %rax                              #105.36
        setb      %sil                                          #104.34
        movl      %esi, 32(%rsp)                                #104.34[spill]
        movq      $0xffffffff00000001, %rsi                     #107.36
        mulx      %rsi, %r14, %rsi                              #107.36
        movl      %r9d, %edx                                    #108.34
        adox      %r9d, %edx                                    #108.34
        movq      %rbx, %rdx                                    #118.36
        adox      %rcx, %rax                                    #108.34
        movl      %r9d, %ecx                                    #110.34
        adox      %r13, %rdi                                    #109.34
        adox      %r13, %r14                                    #110.34
        seto      %cl                                           #110.34
        clc                                                     #111.31
        adcx      %rsi, %rcx                                    #111.31
        movl      %r9d, %esi                                    #112.31
        adox      %r9d, %esi                                    #112.31
        adox      %r15, %r8                                     #112.31
        adox      %rax, %r12                                    #113.34
        mulx      136(%rsp), %r8, %rax                          #118.36[spill]
        adox      %rdi, %r11                                    #114.34
        movl      %r9d, %edi                                    #116.34
        adox      %r14, %r10                                    #115.34
        mulx      160(%rsp), %r14, %r15                         #119.36[spill]
        adox      %rcx, %rbp                                    #116.34
        mulx      %rbx, %rcx, %rsi                              #120.36
        seto      %dil                                          #116.34
        clc                                                     #122.34
        adcx      %r14, %rax                                    #122.34
        adcx      %rcx, %r15                                    #123.34
        movq      144(%rsp), %rcx                               #121.36[spill]
        mulx      %rcx, %rbx, %r14                              #121.36
        movl      %r9d, %edx                                    #125.31
        adcx      %rbx, %rsi                                    #124.34
        movl      %r9d, %ebx                                    #124.34
        setb      %bl                                           #124.34
        adox      %r9d, %edx                                    #125.31
        adox      %r14, %rbx                                    #125.31
        clc                                                     #126.34
        adcx      %r8, %r12                                     #126.34
        movl      %r9d, %r8d                                    #129.34
        movq      %r12, %rdx                                    #131.36
        adcx      %rax, %r11                                    #127.34
        movl      32(%rsp), %eax                                #130.34[spill]
        adcx      %r15, %r10                                    #128.34
        movq      $0x0ffffffff, %r15                            #132.36
        adcx      %rsi, %rbp                                    #129.34
        setb      %r8b                                          #129.34
        xorl      %r14d, %r14d                                  #129.34
        addl      %edi, %eax                                    #130.34
        cmpl      %r8d, %r9d                                    #130.34
        movq      $0xffffffff00000001, %rdi                     #133.36
        mulx      %rdi, %rdi, %rsi                              #133.36
        adcx      %rbx, %rax                                    #130.34
        movq      $-1, %rbx                                     #131.36
        setb      %r14b                                         #130.34
        movl      %r14d, 40(%rsp)                               #130.34[spill]
        mulx      %rbx, %r8, %r14                               #131.36
        mulx      %r15, %r15, %rbx                              #132.36
        movl      %r9d, %edx                                    #134.34
        adox      %r9d, %edx                                    #134.34
        movq      %rcx, %rdx                                    #144.36
        adox      %r15, %r14                                    #134.34
        movl      %r9d, %r15d                                   #136.34
        adox      %r13, %rbx                                    #135.34
        adox      %r13, %rdi                                    #136.34
        seto      %r15b                                         #136.34
        clc                                                     #137.31
        adcx      %rsi, %r15                                    #137.31
        movl      %r9d, %esi                                    #138.31
        adox      %r9d, %esi                                    #138.31
        movl      %r9d, %esi                                    #142.34
        adox      %r8, %r12                                     #138.31
        adox      %r14, %r11                                    #139.34
        adox      %rbx, %r10                                    #140.34
        movl      %r9d, %ebx                                    #150.34
        adox      %rdi, %rbp                                    #141.34
        mulx      160(%rsp), %r8, %rdi                          #145.36[spill]
        adox      %r15, %rax                                    #142.34
        mulx      136(%rsp), %r15, %r12                         #144.36[spill]
        seto      %sil                                          #142.34
        clc                                                     #148.34
        adcx      %r8, %r12                                     #148.34
        mulx      152(%rsp), %r14, %r8                          #146.36[spill]
        adcx      %r14, %rdi                                    #149.34
        mulx      %rcx, %rcx, %r14                              #147.36
        adcx      %rcx, %r8                                     #150.34
        movl      %r9d, %ecx                                    #151.31
        setb      %bl                                           #150.34
        adox      %r9d, %ecx                                    #151.31
        movq      $-1, %rcx                                     #157.36
        adox      %r14, %rbx                                    #151.31
        clc                                                     #152.34
        movl      40(%rsp), %r14d                               #156.34[spill]
        adcx      %r15, %r11                                    #152.34
        movq      $0xffffffff00000001, %r15                     #159.36
        movq      %r11, %rdx                                    #157.36
        adcx      %r12, %r10                                    #153.34
        movl      %r9d, %r12d                                   #155.34
        adcx      %rdi, %rbp                                    #154.34
        adcx      %r8, %rax                                     #155.34
        mulx      %rcx, %r8, %rcx                               #157.36
        setb      %r12b                                         #155.34
        addl      %esi, %r14d                                   #156.34
        cmpl      %r12d, %r9d                                   #156.34
        movq      $0x0ffffffff, %r12                            #158.36
        mulx      %r12, %rdi, %r12                              #158.36
        adcx      %rbx, %r14                                    #156.34
        movl      %r9d, %ebx                                    #156.34
        mulx      %r15, %r15, %rsi                              #159.36
        movl      %r9d, %edx                                    #160.34
        setb      %bl                                           #156.34
        adox      %r9d, %edx                                    #160.34
        adox      %rdi, %rcx                                    #160.34
        movl      %r9d, %edi                                    #162.34
        adox      %r13, %r12                                    #161.34
        adox      %r13, %r15                                    #162.34
        seto      %dil                                          #162.34
        clc                                                     #163.31
        adcx      %rsi, %rdi                                    #163.31
        movl      %r9d, %esi                                    #164.31
        adox      %r9d, %esi                                    #164.31
        adox      %r8, %r11                                     #164.31
        movq      $0x0ffffffff, %r8                             #171.34
        movl      %r9d, %r11d                                   #168.34
        adox      %rcx, %r10                                    #165.34
        movq      $0xffffffff00000001, %rcx                     #173.34
        movq      %r10, %rdx                                    #170.34
        adox      %r12, %rbp                                    #166.34
        adox      %r15, %rax                                    #167.34
        adox      %rdi, %r14                                    #168.34
        movq      %rax, %rdi                                    #172.34
        movq      %r14, %rsi                                    #173.34
        seto      %r11b                                         #168.34
        addl      %r11d, %ebx                                   #174.31
        movq      $-1, %r11                                     #170.34
        subq      %r11, %rdx                                    #170.34
        movq      %rbp, %r11                                    #171.34
        sbbq      %r8, %r11                                     #171.34
        sbbq      %r13, %rdi                                    #172.34
        sbbq      %rcx, %rsi                                    #173.34
        movl      %r9d, %ecx                                    #173.34
        setb      %cl                                           #173.34
        cmpl      %ecx, %r9d                                    #174.31
        sbbq      %r13, %rbx                                    #174.31
        setb      %r9b                                          #174.31
        testq     %r9, %r9                                      #18.0
        cmovnz    %r14, %rsi                                    #18.0
        movq      %rsi, 248(%rsp)                               #18.0[spill]
        testq     %r9, %r9                                      #18.0
        cmovnz    %rax, %rdi                                    #18.0
        movq      %rdi, 256(%rsp)                               #18.0[spill]
        testq     %r9, %r9                                      #18.0
        cmovnz    %rbp, %r11                                    #18.0
        movq      %r11, 264(%rsp)                               #18.0[spill]
        testq     %r9, %r9                                      #18.0
        cmovnz    %r10, %rdx                                    #18.0
        movq      %rdx, 272(%rsp)                               #18.0[spill]
        movq      %rsi, 64(%rsp)                                #217.37
        movq      %rdi, 72(%rsp)                                #217.37
        movq      %r11, 80(%rsp)                                #217.37
        movq      %rdx, 88(%rsp)                                #217.37
        vmovups   %xmm0, (%rsp)                                 #218.20
        vmovups   %xmm0, 16(%rsp)                               #218.20
        movq      168(%rsp), %r12                               #72.34[spill]
        movq      %r12, %rdx                                    #72.34
        movq      184(%rsp), %r13                               #73.34[spill]
        xorl      %r11d, %r11d                                  #76.32
        xorl      %ebx, %ebx                                    #76.32
        xorl      %r9d, %r9d                                    #76.32
        mulx      %r12, %r15, %r14                              #72.34
        mulx      %r13, %r10, %rsi                              #73.34
        adcx      %r10, %r14                                    #76.32
        movq      $-1, %r10                                     #80.34
        vpxor     %xmm0, %xmm0, %xmm0                           #219.21
        mulx      176(%rsp), %rdi, %r8                          #74.34[spill]
        adcx      %rdi, %rsi                                    #77.32
        movq      $0xffffffff00000001, %rdi                     #82.34
        mulx      192(%rsp), %rcx, %rax                         #75.34[spill]
        movq      %r15, %rdx                                    #80.34
        adcx      %rcx, %r8                                     #78.32
        mulx      %rdi, %rcx, %rdi                              #82.34
        setb      %r9b                                          #78.32
        adox      %r11d, %ebx                                   #79.30
        adox      %rax, %r9                                     #79.30
        mulx      %r10, %rbp, %rax                              #80.34
        movq      $0x0ffffffff, %r10                            #81.34
        clc                                                     #83.32
        mulx      %r10, %r10, %rbx                              #81.34
        movl      %r11d, %edx                                   #86.30
        adcx      %r10, %rax                                    #83.32
        movl      $0, %r10d                                     #84.32
        adcx      %r10, %rbx                                    #84.32
        adcx      %r10, %rcx                                    #85.32
        movl      %r11d, %r10d                                  #85.32
        setb      %r10b                                         #85.32
        adox      %r11d, %edx                                   #86.30
        movq      %r13, %rdx                                    #92.34
        adox      %rdi, %r10                                    #86.30
        movl      %r11d, %edi                                   #86.30
        seto      %dil                                          #86.30
        clc                                                     #87.30
        adcx      %rbp, %r15                                    #87.30
        adcx      %rax, %r14                                    #88.32
        adcx      %rbx, %rsi                                    #89.32
        mulx      %r13, %rbx, %r15                              #93.34
        movl      %r11d, %r13d                                  #96.32
        adcx      %rcx, %r8                                     #90.32
        mulx      %r12, %rbp, %rcx                              #92.34
        adcx      %r10, %r9                                     #91.32
        movl      %r11d, %r10d                                  #91.32
        mulx      176(%rsp), %rax, %r12                         #94.34[spill]
        setb      %r10b                                         #91.32
        adox      %r11d, %r13d                                  #96.32
        mulx      192(%rsp), %rdx, %rdi                         #95.34[spill]
        adox      %rbx, %rcx                                    #96.32
        movl      %r11d, %ebx                                   #98.32
        adox      %rax, %r15                                    #97.32
        movl      %r11d, %eax                                   #100.34
        adox      %rdx, %r12                                    #98.32
        seto      %bl                                           #98.32
        clc                                                     #99.30
        adcx      %rdi, %rbx                                    #99.30
        adox      %r11d, %eax                                   #100.34
        movl      %r11d, %edi                                   #104.34
        adox      %rbp, %r14                                    #100.34
        movq      %r14, %rdx                                    #105.36
        adox      %rcx, %rsi                                    #101.34
        movq      $0x0ffffffff, %rcx                            #106.36
        adox      %r15, %r8                                     #102.34
        mulx      %rcx, %r15, %rax                              #106.36
        adox      %r12, %r9                                     #103.34
        movq      $-1, %r12                                     #105.36
        mulx      %r12, %rbp, %r13                              #105.36
        movl      $0, %r12d                                     #109.34
        adox      %rbx, %r10                                    #104.34
        movq      $0xffffffff00000001, %rbx                     #107.36
        mulx      %rbx, %rbx, %rcx                              #107.36
        seto      %dil                                          #104.34
        clc                                                     #108.34
        movq      176(%rsp), %rdx                               #118.36[spill]
        adcx      %r15, %r13                                    #108.34
        movl      %r11d, %r15d                                  #110.34
        adcx      %r12, %rax                                    #109.34
        adcx      %r12, %rbx                                    #110.34
        movl      %r11d, %r12d                                  #111.31
        setb      %r15b                                         #110.34
        adox      %r11d, %r12d                                  #111.31
        adox      %rcx, %r15                                    #111.31
        clc                                                     #112.31
        adcx      %rbp, %r14                                    #112.31
        movl      %r11d, %r14d                                  #116.34
        adcx      %r13, %rsi                                    #113.34
        mulx      168(%rsp), %r13, %rbp                         #118.36[spill]
        adcx      %rax, %r8                                     #114.34
        mulx      %rdx, %rax, %r12                              #120.36
        adcx      %rbx, %r9                                     #115.34
        adcx      %r15, %r10                                    #116.34
        mulx      184(%rsp), %rcx, %r15                         #119.36[spill]
        setb      %r14b                                         #116.34
        movl      %r14d, 64(%rsp)                               #116.34[spill]
        movl      %r11d, %r14d                                  #122.34
        adox      %r11d, %r14d                                  #122.34
        mulx      192(%rsp), %rdx, %rbx                         #121.36[spill]
        adox      %rcx, %rbp                                    #122.34
        movl      %r11d, %ecx                                   #124.34
        adox      %rax, %r15                                    #123.34
        movl      %r11d, %eax                                   #126.34
        adox      %rdx, %r12                                    #124.34
        seto      %cl                                           #124.34
        clc                                                     #125.31
        adcx      %rbx, %rcx                                    #125.31
        adox      %r11d, %eax                                   #126.34
        adox      %r13, %rsi                                    #126.34
        movq      $0x0ffffffff, %r13                            #132.36
        movq      %rsi, %rdx                                    #131.36
        adox      %rbp, %r8                                     #127.34
        movl      %r11d, %ebp                                   #129.34
        adox      %r15, %r9                                     #128.34
        mulx      %r13, %r13, %r15                              #132.36
        adox      %r12, %r10                                    #129.34
        movq      $0xffffffff00000001, %r12                     #133.36
        mulx      %r12, %r14, %r12                              #133.36
        seto      %bpl                                          #129.34
        xorl      %ebx, %ebx                                    #129.34
        addl      64(%rsp), %edi                                #130.34[spill]
        cmpl      %ebp, %r11d                                   #130.34
        adcx      %rcx, %rdi                                    #130.34
        movq      $-1, %rcx                                     #131.36
        mulx      %rcx, %rbp, %rax                              #131.36
        movl      %r11d, %edx                                   #134.34
        setb      %bl                                           #130.34
        adox      %r11d, %edx                                   #134.34
        movq      192(%rsp), %rdx                               #144.36[spill]
        adox      %r13, %rax                                    #134.34
        movl      $0, %r13d                                     #135.34
        adox      %r13, %r15                                    #135.34
        adox      %r13, %r14                                    #136.34
        movl      %r11d, %r13d                                  #136.34
        seto      %r13b                                         #136.34
        clc                                                     #137.31
        adcx      %r12, %r13                                    #137.31
        movl      %r11d, %r12d                                  #138.31
        adox      %r11d, %r12d                                  #138.31
        adox      %rbp, %rsi                                    #138.31
        mulx      184(%rsp), %rbp, %rsi                         #145.36[spill]
        adox      %rax, %r8                                     #139.34
        movl      %r11d, %eax                                   #142.34
        adox      %r15, %r9                                     #140.34
        adox      %r14, %r10                                    #141.34
        mulx      168(%rsp), %r12, %r14                         #144.36[spill]
        adox      %r13, %rdi                                    #142.34
        mulx      176(%rsp), %r15, %r13                         #146.36[spill]
        seto      %al                                           #142.34
        clc                                                     #148.34
        adcx      %rbp, %r14                                    #148.34
        adcx      %r15, %rsi                                    #149.34
        mulx      %rdx, %rbp, %r15                              #147.36
        movl      %r11d, %edx                                   #151.31
        adcx      %rbp, %r13                                    #150.34
        movl      %r11d, %ebp                                   #150.34
        setb      %bpl                                          #150.34
        adox      %r11d, %edx                                   #151.31
        adox      %r15, %rbp                                    #151.31
        clc                                                     #152.34
        adcx      %r12, %r8                                     #152.34
        movq      %r8, %rdx                                     #157.36
        adcx      %r14, %r9                                     #153.34
        movq      $0xffffffff00000001, %r14                     #159.36
        adcx      %rsi, %r10                                    #154.34
        movl      %r11d, %esi                                   #155.34
        adcx      %r13, %rdi                                    #155.34
        mulx      %rcx, %r15, %r13                              #157.36
        setb      %sil                                          #155.34
        addl      %eax, %ebx                                    #156.34
        cmpl      %esi, %r11d                                   #156.34
        movq      $0x0ffffffff, %rax                            #158.36
        mulx      %rax, %rax, %r12                              #158.36
        adcx      %rbp, %rbx                                    #156.34
        movl      %r11d, %ebp                                   #156.34
        mulx      %r14, %r14, %rsi                              #159.36
        movl      %r11d, %edx                                   #160.34
        setb      %bpl                                          #156.34
        adox      %r11d, %edx                                   #160.34
        movl      %r11d, %edx                                   #162.34
        adox      %rax, %r13                                    #160.34
        movl      $0, %eax                                      #161.34
        adox      %rax, %r12                                    #161.34
        adox      %rax, %r14                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %rsi, %rdx                                    #163.31
        movl      %r11d, %esi                                   #164.31
        adox      %r11d, %esi                                   #164.31
        adox      %r15, %r8                                     #164.31
        movl      %r11d, %r8d                                   #168.34
        adox      %r13, %r9                                     #165.34
        adox      %r12, %r10                                    #166.34
        movq      $0xffffffff00000001, %r12                     #173.34
        adox      %r14, %rdi                                    #167.34
        movq      %rdi, %r15                                    #172.34
        adox      %rdx, %rbx                                    #168.34
        movq      %r9, %rdx                                     #170.34
        seto      %r8b                                          #168.34
        xorl      %r13d, %r13d                                  #168.34
        addl      %r8d, %ebp                                    #174.31
        subq      %rcx, %rdx                                    #170.34
        movq      %r10, %rcx                                    #171.34
        movq      $0x0ffffffff, %r8                             #171.34
        sbbq      %r8, %rcx                                     #171.34
        movq      %rbx, %r8                                     #173.34
        sbbq      %rax, %r15                                    #172.34
        sbbq      %r12, %r8                                     #173.34
        setb      %r13b                                         #173.34
        cmpl      %r13d, %r11d                                  #174.31
        sbbq      %rax, %rbp                                    #174.31
        setb      %r11b                                         #174.31
        testq     %r11, %r11                                    #18.0
        cmovnz    %rbx, %r8                                     #18.0
        testq     %r11, %r11                                    #18.0
        cmovnz    %rdi, %r15                                    #18.0
        movq      %r15, 232(%rsp)                               #18.0[spill]
        testq     %r11, %r11                                    #18.0
        cmovnz    %r10, %rcx                                    #18.0
        testq     %r11, %r11                                    #18.0
        cmovnz    %r9, %rdx                                     #18.0
        movq      %rdx, 240(%rsp)                               #18.0[spill]
        movq      %r8, (%rsp)                                   #218.37
        movq      %r15, 8(%rsp)                                 #218.37
        movq      %rcx, 16(%rsp)                                #218.37
        movq      %rdx, 24(%rsp)                                #218.37
        vmovups   %xmm0, 32(%rsp)                               #219.21
        vmovups   %xmm0, 48(%rsp)                               #219.21
        movq      272(%rsp), %rdx                               #72.34[spill]
        xorl      %r12d, %r12d                                  #76.32
        xorl      %ebp, %ebp                                    #76.32
        vpxor     %xmm0, %xmm0, %xmm0                           #228.21
        movq      136(%rsp), %r9                                #72.34[spill]
        movq      160(%rsp), %r10                               #73.34[spill]
        movq      %r8, 64(%rsp)                                 #[spill]
        mulx      %r9, %r13, %r11                               #72.34
        mulx      %r10, %r8, %rbx                               #73.34
        adcx      %r8, %r11                                     #76.32
        movl      %ebp, %r8d                                    #78.32
        mulx      152(%rsp), %rsi, %rdi                         #74.34[spill]
        adcx      %rsi, %rbx                                    #77.32
        movq      $-1, %rsi                                     #80.34
        mulx      144(%rsp), %rax, %r15                         #75.34[spill]
        movq      %r13, %rdx                                    #80.34
        adcx      %rax, %rdi                                    #78.32
        movq      $0xffffffff00000001, %rax                     #82.34
        movq      %rcx, 72(%rsp)                                #[spill]
        movl      %ebp, %ecx                                    #79.30
        setb      %r8b                                          #78.32
        adox      %ebp, %ecx                                    #79.30
        adox      %r15, %r8                                     #79.30
        mulx      %rax, %rcx, %rax                              #82.34
        seto      %r12b                                         #79.30
        mulx      %rsi, %r14, %r12                              #80.34
        movq      $0x0ffffffff, %rsi                            #81.34
        clc                                                     #83.32
        mulx      %rsi, %rsi, %r15                              #81.34
        movl      %ebp, %edx                                    #86.30
        adcx      %rsi, %r12                                    #83.32
        movl      $0, %esi                                      #84.32
        adcx      %rsi, %r15                                    #84.32
        adcx      %rsi, %rcx                                    #85.32
        movl      %ebp, %esi                                    #85.32
        setb      %sil                                          #85.32
        adox      %ebp, %edx                                    #86.30
        adox      %rax, %rsi                                    #86.30
        movl      %ebp, %eax                                    #86.30
        movq      264(%rsp), %rdx                               #92.34[spill]
        seto      %al                                           #86.30
        clc                                                     #87.30
        adcx      %r14, %r13                                    #87.30
        movl      %ebp, %r13d                                   #96.32
        adcx      %r12, %r11                                    #88.32
        mulx      %r9, %r14, %r12                               #92.34
        adcx      %r15, %rbx                                    #89.32
        mulx      152(%rsp), %r15, %r9                          #94.34[spill]
        adcx      %rcx, %rdi                                    #90.32
        mulx      %r10, %rcx, %r10                              #93.34
        adcx      %rsi, %r8                                     #91.32
        movl      %ebp, %esi                                    #91.32
        mulx      144(%rsp), %rdx, %rax                         #95.34[spill]
        setb      %sil                                          #91.32
        adox      %ebp, %r13d                                   #96.32
        adox      %rcx, %r12                                    #96.32
        movl      %ebp, %ecx                                    #98.32
        adox      %r15, %r10                                    #97.32
        movl      %ebp, %r15d                                   #100.34
        adox      %rdx, %r9                                     #98.32
        seto      %cl                                           #98.32
        clc                                                     #99.30
        adcx      %rax, %rcx                                    #99.30
        adox      %ebp, %r15d                                   #100.34
        movl      %ebp, %eax                                    #104.34
        adox      %r14, %r11                                    #100.34
        movq      $0x0ffffffff, %r14                            #106.36
        movq      %r11, %rdx                                    #105.36
        adox      %r12, %rbx                                    #101.34
        movq      $0xffffffff00000001, %r12                     #107.36
        adox      %r10, %rdi                                    #102.34
        movq      $-1, %r10                                     #105.36
        adox      %r9, %r8                                      #103.34
        mulx      %r10, %r10, %r9                               #105.36
        adox      %rcx, %rsi                                    #104.34
        mulx      %r14, %rcx, %r15                              #106.36
        movl      $0, %r14d                                     #109.34
        seto      %al                                           #104.34
        clc                                                     #108.34
        adcx      %rcx, %r9                                     #108.34
        mulx      %r12, %r13, %rcx                              #107.36
        movl      %ebp, %r12d                                   #110.34
        adcx      %r14, %r15                                    #109.34
        movq      256(%rsp), %rdx                               #118.36[spill]
        adcx      %r14, %r13                                    #110.34
        movl      %ebp, %r14d                                   #111.31
        setb      %r12b                                         #110.34
        adox      %ebp, %r14d                                   #111.31
        adox      %rcx, %r12                                    #111.31
        clc                                                     #112.31
        mulx      160(%rsp), %rcx, %r14                         #119.36[spill]
        adcx      %r10, %r11                                    #112.31
        mulx      152(%rsp), %r10, %r11                         #120.36[spill]
        adcx      %r9, %rbx                                     #113.34
        movl      %ebp, %r9d                                    #116.34
        adcx      %r15, %rdi                                    #114.34
        adcx      %r13, %r8                                     #115.34
        movl      %ebp, %r13d                                   #122.34
        adcx      %r12, %rsi                                    #116.34
        setb      %r9b                                          #116.34
        adox      %ebp, %r13d                                   #122.34
        movl      %r9d, 80(%rsp)                                #116.34[spill]
        mulx      136(%rsp), %r12, %r9                          #118.36[spill]
        adox      %rcx, %r9                                     #122.34
        movl      %ebp, %ecx                                    #124.34
        mulx      144(%rsp), %rdx, %r15                         #121.36[spill]
        adox      %r10, %r14                                    #123.34
        movl      %ebp, %r10d                                   #126.34
        adox      %rdx, %r11                                    #124.34
        seto      %cl                                           #124.34
        clc                                                     #125.31
        adcx      %r15, %rcx                                    #125.31
        adox      %ebp, %r10d                                   #126.34
        movq      $0x0ffffffff, %r10                            #132.36
        adox      %r12, %rbx                                    #126.34
        movq      %rbx, %rdx                                    #131.36
        adox      %r9, %rdi                                     #127.34
        mulx      %r10, %r9, %r12                               #132.36
        adox      %r14, %r8                                     #128.34
        adox      %r11, %rsi                                    #129.34
        movl      %ebp, %r11d                                   #129.34
        seto      %r11b                                         #129.34
        xorl      %r15d, %r15d                                  #129.34
        addl      80(%rsp), %eax                                #130.34[spill]
        cmpl      %r11d, %ebp                                   #130.34
        movq      $0xffffffff00000001, %r11                     #133.36
        adcx      %rcx, %rax                                    #130.34
        movq      $-1, %rcx                                     #131.36
        mulx      %rcx, %r14, %r13                              #131.36
        mulx      %r11, %r10, %r11                              #133.36
        movl      %ebp, %edx                                    #134.34
        setb      %r15b                                         #130.34
        adox      %ebp, %edx                                    #134.34
        movq      248(%rsp), %rdx                               #144.36[spill]
        adox      %r9, %r13                                     #134.34
        movl      $0, %r9d                                      #135.34
        adox      %r9, %r12                                     #135.34
        adox      %r9, %r10                                     #136.34
        movl      %ebp, %r9d                                    #136.34
        seto      %r9b                                          #136.34
        clc                                                     #137.31
        adcx      %r11, %r9                                     #137.31
        movl      %ebp, %r11d                                   #138.31
        adox      %ebp, %r11d                                   #138.31
        adox      %r14, %rbx                                    #138.31
        adox      %r13, %rdi                                    #139.34
        mulx      136(%rsp), %r13, %r11                         #144.36[spill]
        adox      %r12, %r8                                     #140.34
        mulx      160(%rsp), %r12, %rbx                         #145.36[spill]
        adox      %r10, %rsi                                    #141.34
        movl      %ebp, %r10d                                   #142.34
        adox      %r9, %rax                                     #142.34
        seto      %r10b                                         #142.34
        clc                                                     #148.34
        adcx      %r12, %r11                                    #148.34
        mulx      152(%rsp), %r14, %r12                         #146.36[spill]
        adcx      %r14, %rbx                                    #149.34
        mulx      144(%rsp), %r9, %r14                          #147.36[spill]
        movl      %ebp, %edx                                    #151.31
        adcx      %r9, %r12                                     #150.34
        movl      %ebp, %r9d                                    #150.34
        setb      %r9b                                          #150.34
        adox      %ebp, %edx                                    #151.31
        adox      %r14, %r9                                     #151.31
        clc                                                     #152.34
        adcx      %r13, %rdi                                    #152.34
        movq      $0xffffffff00000001, %r13                     #159.36
        movq      %rdi, %rdx                                    #157.36
        adcx      %r11, %r8                                     #153.34
        adcx      %rbx, %rsi                                    #154.34
        movl      %ebp, %ebx                                    #155.34
        adcx      %r12, %rax                                    #155.34
        mulx      %rcx, %r14, %r12                              #157.36
        setb      %bl                                           #155.34
        addl      %r10d, %r15d                                  #156.34
        cmpl      %ebx, %ebp                                    #156.34
        movq      $0x0ffffffff, %r10                            #158.36
        mulx      %r10, %r10, %r11                              #158.36
        adcx      %r9, %r15                                     #156.34
        movl      %ebp, %r9d                                    #156.34
        mulx      %r13, %r13, %rbx                              #159.36
        movl      %ebp, %edx                                    #160.34
        setb      %r9b                                          #156.34
        adox      %ebp, %edx                                    #160.34
        movl      %ebp, %edx                                    #162.34
        adox      %r10, %r12                                    #160.34
        movl      $0, %r10d                                     #161.34
        adox      %r10, %r11                                    #161.34
        adox      %r10, %r13                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %rbx, %rdx                                    #163.31
        movl      %ebp, %ebx                                    #164.31
        adox      %ebp, %ebx                                    #164.31
        adox      %r14, %rdi                                    #164.31
        movl      %ebp, %edi                                    #168.34
        adox      %r12, %r8                                     #165.34
        movq      $0xffffffff00000001, %r12                     #173.34
        adox      %r11, %rsi                                    #166.34
        movq      $0x0ffffffff, %r11                            #171.34
        adox      %r13, %rax                                    #167.34
        movq      %rax, %rbx                                    #172.34
        adox      %rdx, %r15                                    #168.34
        movq      %r15, %rdx                                    #173.34
        seto      %dil                                          #168.34
        xorl      %r14d, %r14d                                  #168.34
        addl      %edi, %r9d                                    #174.31
        movq      %r8, %rdi                                     #170.34
        subq      %rcx, %rdi                                    #170.34
        movq      %rsi, %rcx                                    #171.34
        sbbq      %r11, %rcx                                    #171.34
        sbbq      %r10, %rbx                                    #172.34
        sbbq      %r12, %rdx                                    #173.34
        setb      %r14b                                         #173.34
        cmpl      %r14d, %ebp                                   #174.31
        sbbq      %r10, %r9                                     #174.31
        setb      %bpl                                          #174.31
        movl      $1, %r10d                                     #174.31
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %r15, %rdx                                    #18.0
        movq      $0xffffffff00000000, %r15                     #18.0
        movq      %rdx, 200(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rax, %rbx                                    #18.0
        movq      %rbx, 208(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %rsi, %rcx                                    #18.0
        movq      %rcx, 224(%rsp)                               #18.0[spill]
        testq     %rbp, %rbp                                    #18.0
        cmovnz    %r8, %rdi                                     #18.0
        movq      112(%rsp), %r8                                #18.0[spill]
        movq      %rdi, 216(%rsp)                               #18.0[spill]
        movq      %rdi, 56(%rsp)                                #219.35
        movq      %rdx, 32(%rsp)                                #219.35
        movq      $0x0fffffffe, %rdx                            #18.0
        movq      %rbx, 40(%rsp)                                #219.35
        movq      %rcx, 48(%rsp)                                #219.35
        movq      88(%r8), %rax                                 #18.0
        movq      96(%rsp), %rdi                                #18.0[spill]
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %rax, %r10                                    #18.0
        movq      $-1, %rax                                     #18.0
        movq      %r10, 88(%r8)                                 #220.5
        movq      80(%r8), %rcx                                 #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %rcx, %r15                                    #18.0
        movq      %r15, 80(%r8)                                 #221.5
        movq      72(%r8), %rsi                                 #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %rsi, %rax                                    #18.0
        movq      %rax, 72(%r8)                                 #222.5
        movq      64(%r8), %r9                                  #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %r9, %rdx                                     #18.0
        movq      120(%rsp), %r11                               #18.0[spill]
        movq      %rdx, 64(%r8)                                 #223.5
        movq      128(%rsp), %r12                               #18.0[spill]
        movq      88(%r11), %r13                                #18.0
        testq     %r12, %r12                                    #18.0
        cmovnz    %r10, %r13                                    #18.0
        movq      %r13, 88(%r8)                                 #18.0
        movq      80(%r11), %r10                                #18.0
        testq     %r12, %r12                                    #18.0
        cmovnz    %r15, %r10                                    #18.0
        movq      %r10, 80(%r8)                                 #18.0
        movq      72(%r11), %r13                                #18.0
        testq     %r12, %r12                                    #18.0
        cmovnz    %rax, %r13                                    #18.0
        movq      %r13, 72(%r8)                                 #18.0
        movq      64(%r11), %rcx                                #18.0
        testq     %r12, %r12                                    #18.0
        cmovnz    %rdx, %rcx                                    #18.0
        movq      %rcx, 64(%r8)                                 #18.0
        vmovups   %xmm0, (%rsp)                                 #228.21
        vmovups   %xmm0, 16(%rsp)                               #228.21
        movq      72(%rsp), %rcx                                #228.21[spill]
        movq      64(%rsp), %r8                                 #228.21[spill]
        xorl      %r9d, %r9d                                    #76.32
        movq      272(%rsp), %rdx                               #72.34[spill]
        xorl      %r14d, %r14d                                  #79.30
        movq      %r8, 64(%rsp)                                 #[spill]
        xorl      %r8d, %r8d                                    #76.32
        vpxor     %xmm0, %xmm0, %xmm0                           #229.21
        movq      %rcx, 72(%rsp)                                #[spill]
        mulx      24(%r11), %r13, %r12                          #72.34
        mulx      16(%r11), %r10, %rcx                          #73.34
        adcx      %r10, %r12                                    #76.32
        movl      %r9d, %r10d                                   #79.30
        mulx      8(%r11), %rsi, %rdi                           #74.34
        adcx      %rsi, %rcx                                    #77.32
        movq      $-1, %rsi                                     #80.34
        mulx      (%r11), %rax, %r15                            #75.34
        movq      %r13, %rdx                                    #80.34
        adcx      %rax, %rdi                                    #78.32
        movq      $0x0ffffffff, %rax                            #81.34
        mulx      %rsi, %rbp, %rbx                              #80.34
        setb      %r8b                                          #78.32
        adox      %r9d, %r14d                                   #79.30
        adox      %r15, %r8                                     #79.30
        movq      $0xffffffff00000001, %r15                     #82.34
        mulx      %rax, %r14, %rax                              #81.34
        seto      %r10b                                         #79.30
        clc                                                     #83.32
        mulx      %r15, %rsi, %r10                              #82.34
        movl      %r9d, %r15d                                   #86.30
        adcx      %r14, %rbx                                    #83.32
        movl      $0, %r14d                                     #84.32
        movq      264(%rsp), %rdx                               #92.34[spill]
        adcx      %r14, %rax                                    #84.32
        adcx      %r14, %rsi                                    #85.32
        movl      %r9d, %r14d                                   #85.32
        setb      %r14b                                         #85.32
        adox      %r9d, %r15d                                   #86.30
        adox      %r10, %r14                                    #86.30
        clc                                                     #87.30
        movl      %r9d, %r10d                                   #91.32
        adcx      %rbp, %r13                                    #87.30
        mulx      16(%r11), %r13, %rbp                          #93.34
        adcx      %rbx, %r12                                    #88.32
        adcx      %rax, %rcx                                    #89.32
        mulx      24(%r11), %rbx, %rax                          #92.34
        adcx      %rsi, %rdi                                    #90.32
        adcx      %r14, %r8                                     #91.32
        mulx      8(%r11), %r15, %r14                           #94.34
        mulx      (%r11), %rdx, %rsi                            #95.34
        movl      %r9d, %r11d                                   #96.32
        setb      %r10b                                         #91.32
        adox      %r9d, %r11d                                   #96.32
        adox      %r13, %rax                                    #96.32
        movl      %r9d, %r13d                                   #98.32
        adox      %r15, %rbp                                    #97.32
        movl      %r9d, %r15d                                   #100.34
        adox      %rdx, %r14                                    #98.32
        seto      %r13b                                         #98.32
        clc                                                     #99.30
        adcx      %rsi, %r13                                    #99.30
        adox      %r9d, %r15d                                   #100.34
        movl      %r9d, %esi                                    #104.34
        adox      %rbx, %r12                                    #100.34
        movq      $0x0ffffffff, %rbx                            #106.36
        movq      %r12, %rdx                                    #105.36
        adox      %rax, %rcx                                    #101.34
        movq      $-1, %rax                                     #105.36
        adox      %rbp, %rdi                                    #102.34
        mulx      %rax, %r11, %rbp                              #105.36
        adox      %r14, %r8                                     #103.34
        movl      $0, %r14d                                     #109.34
        mulx      %rbx, %rbx, %rax                              #106.36
        adox      %r13, %r10                                    #104.34
        movq      $0xffffffff00000001, %r13                     #107.36
        seto      %sil                                          #104.34
        clc                                                     #108.34
        adcx      %rbx, %rbp                                    #108.34
        mulx      %r13, %r15, %rbx                              #107.36
        movl      %r9d, %r13d                                   #110.34
        adcx      %r14, %rax                                    #109.34
        movq      256(%rsp), %rdx                               #118.36[spill]
        adcx      %r14, %r15                                    #110.34
        movl      %r9d, %r14d                                   #111.31
        setb      %r13b                                         #110.34
        adox      %r9d, %r14d                                   #111.31
        adox      %rbx, %r13                                    #111.31
        movl      %r9d, %ebx                                    #111.31
        seto      %bl                                           #111.31
        clc                                                     #112.31
        adcx      %r11, %r12                                    #112.31
        adcx      %rbp, %rcx                                    #113.34
        movl      %r9d, %ebp                                    #116.34
        adcx      %rax, %rdi                                    #114.34
        adcx      %r15, %r8                                     #115.34
        movq      120(%rsp), %r15                               #118.36[spill]
        adcx      %r13, %r10                                    #116.34
        mulx      16(%r15), %rax, %r12                          #119.36
        setb      %bpl                                          #116.34
        movl      %ebp, 80(%rsp)                                #116.34[spill]
        mulx      24(%r15), %r13, %rbp                          #118.36
        mulx      8(%r15), %r11, %r14                           #120.36
        mulx      (%r15), %rdx, %rbx                            #121.36
        movl      %r9d, %r15d                                   #122.34
        adox      %r9d, %r15d                                   #122.34
        adox      %rax, %rbp                                    #122.34
        movl      %r9d, %eax                                    #124.34
        adox      %r11, %r12                                    #123.34
        adox      %rdx, %r14                                    #124.34
        seto      %al                                           #124.34
        clc                                                     #125.31
        adcx      %rbx, %rax                                    #125.31
        movl      %r9d, %ebx                                    #126.34
        adox      %r9d, %ebx                                    #126.34
        movq      $0x0ffffffff, %r11                            #132.36
        adox      %r13, %rcx                                    #126.34
        movq      %rcx, %rdx                                    #131.36
        adox      %rbp, %rdi                                    #127.34
        movq      $0xffffffff00000001, %rbp                     #133.36
        mulx      %r11, %r11, %r13                              #132.36
        adox      %r12, %r8                                     #128.34
        movl      %r9d, %r12d                                   #129.34
        adox      %r14, %r10                                    #129.34
        seto      %r12b                                         #129.34
        xorl      %ebx, %ebx                                    #129.34
        addl      80(%rsp), %esi                                #130.34[spill]
        cmpl      %r12d, %r9d                                   #130.34
        mulx      %rbp, %rbp, %r12                              #133.36
        adcx      %rax, %rsi                                    #130.34
        movq      $-1, %rax                                     #131.36
        mulx      %rax, %r15, %r14                              #131.36
        movl      %r9d, %edx                                    #134.34
        setb      %bl                                           #130.34
        adox      %r9d, %edx                                    #134.34
        movq      248(%rsp), %rdx                               #144.36[spill]
        adox      %r11, %r14                                    #134.34
        movl      $0, %r11d                                     #135.34
        adox      %r11, %r13                                    #135.34
        adox      %r11, %rbp                                    #136.34
        movl      %r9d, %r11d                                   #136.34
        seto      %r11b                                         #136.34
        clc                                                     #137.31
        adcx      %r12, %r11                                    #137.31
        movl      %r9d, %r12d                                   #138.31
        adox      %r9d, %r12d                                   #138.31
        adox      %r15, %rcx                                    #138.31
        movq      120(%rsp), %r15                               #144.36[spill]
        adox      %r14, %rdi                                    #139.34
        adox      %r13, %r8                                     #140.34
        mulx      24(%r15), %r14, %r13                          #144.36
        adox      %rbp, %r10                                    #141.34
        movl      %r9d, %ebp                                    #142.34
        adox      %r11, %rsi                                    #142.34
        mulx      16(%r15), %rcx, %r11                          #145.36
        seto      %bpl                                          #142.34
        clc                                                     #148.34
        adcx      %rcx, %r13                                    #148.34
        mulx      8(%r15), %rcx, %r12                           #146.36
        adcx      %rcx, %r11                                    #149.34
        mulx      (%r15), %r15, %rcx                            #147.36
        movl      %r9d, %edx                                    #151.31
        adcx      %r15, %r12                                    #150.34
        movl      %r9d, %r15d                                   #150.34
        setb      %r15b                                         #150.34
        adox      %r9d, %edx                                    #151.31
        adox      %rcx, %r15                                    #151.31
        clc                                                     #152.34
        adcx      %r14, %rdi                                    #152.34
        movq      $0x0ffffffff, %r14                            #158.36
        movq      %rdi, %rdx                                    #157.36
        adcx      %r13, %r8                                     #153.34
        adcx      %r11, %r10                                    #154.34
        movl      %r9d, %r11d                                   #155.34
        adcx      %r12, %rsi                                    #155.34
        mulx      %rax, %r13, %r12                              #157.36
        setb      %r11b                                         #155.34
        addl      %ebp, %ebx                                    #156.34
        xorl      %ebp, %ebp                                    #156.34
        cmpl      %r11d, %r9d                                   #156.34
        mulx      %r14, %rcx, %r11                              #158.36
        movq      $0xffffffff00000001, %r14                     #159.36
        adcx      %r15, %rbx                                    #156.34
        mulx      %r14, %r14, %r15                              #159.36
        movl      %r9d, %edx                                    #160.34
        setb      %bpl                                          #156.34
        adox      %r9d, %edx                                    #160.34
        movl      %r9d, %edx                                    #162.34
        adox      %rcx, %r12                                    #160.34
        movl      $0, %ecx                                      #161.34
        adox      %rcx, %r11                                    #161.34
        adox      %rcx, %r14                                    #162.34
        seto      %dl                                           #162.34
        clc                                                     #163.31
        adcx      %r15, %rdx                                    #163.31
        movl      %r9d, %r15d                                   #164.31
        adox      %r9d, %r15d                                   #164.31
        adox      %r13, %rdi                                    #164.31
        movl      %r9d, %edi                                    #168.34
        adox      %r12, %r8                                     #165.34
        adox      %r11, %r10                                    #166.34
        movq      $0x0ffffffff, %r11                            #171.34
        adox      %r14, %rsi                                    #167.34
        adox      %rdx, %rbx                                    #168.34
        movq      %r8, %rdx                                     #170.34
        movq      %rbx, %r13                                    #173.34
        seto      %dil                                          #168.34
        xorl      %r12d, %r12d                                  #168.34
        addl      %edi, %ebp                                    #174.31
        subq      %rax, %rdx                                    #170.34
        movq      %r10, %rax                                    #171.34
        movq      $0xffffffff00000001, %rdi                     #173.34
        sbbq      %r11, %rax                                    #171.34
        movq      %rsi, %r11                                    #172.34
        sbbq      %rcx, %r11                                    #172.34
        sbbq      %rdi, %r13                                    #173.34
        setb      %r12b                                         #173.34
        cmpl      %r12d, %r9d                                   #174.31
        sbbq      %rcx, %rbp                                    #174.31
        setb      %r9b                                          #174.31
        testq     %r9, %r9                                      #18.0
        cmovnz    %rbx, %r13                                    #18.0
        movq      %r13, 136(%rsp)                               #18.0[spill]
        testq     %r9, %r9                                      #18.0
        cmovnz    %rsi, %r11                                    #18.0
        testq     %r9, %r9                                      #18.0
        cmovnz    %r10, %rax                                    #18.0
        testq     %r9, %r9                                      #18.0
        cmovnz    %r8, %rdx                                     #18.0
        movq      %r13, (%rsp)                                  #228.35
        movq      %r11, 8(%rsp)                                 #228.35
        movq      %rax, 16(%rsp)                                #228.35
        movq      %rdx, 24(%rsp)                                #228.35
        vmovups   %xmm0, 32(%rsp)                               #229.21
        vmovups   %xmm0, 48(%rsp)                               #229.21
        movq      72(%rsp), %rcx                                #229.21[spill]
        movq      64(%rsp), %r8                                 #229.21[spill]
        movq      %r13, %r9                                     #36.32
        movq      %rdx, %r12                                    #33.32
        movq      %rax, %r13                                    #34.32
        xorl      %esi, %esi                                    #33.32
        xorl      %r10d, %r10d                                  #33.32
        movq      %r11, %r14                                    #35.32
        adcx      %rdx, %r12                                    #33.32
        vpxor     %xmm0, %xmm0, %xmm0                           #230.20
        movq      %r12, %r10                                    #37.32
        movq      $0x0ffffffff, %rbx                            #38.32
        adcx      %rax, %r13                                    #34.32
        movq      $0xffffffff00000001, %r15                     #40.32
        adcx      %r11, %r14                                    #35.32
        adcx      %r9, %r9                                      #36.32
        setb      %sil                                          #36.32
        movq      $-1, %rdi                                     #36.32
        xorl      %ebp, %ebp                                    #36.32
        subq      %rdi, %r10                                    #37.32
        movq      %r13, %rdi                                    #38.32
        sbbq      %rbx, %rdi                                    #38.32
        movq      %r14, %rbx                                    #39.32
        sbbq      %rbp, %rbx                                    #39.32
        movq      %r9, %rbp                                     #40.32
        sbbq      %r15, %rbp                                    #40.32
        movl      $0, %r15d                                     #41.30
        sbbq      %r15, %rsi                                    #41.30
        movl      $0, %esi                                      #41.30
        setb      %sil                                          #41.30
        testq     %rsi, %rsi                                    #18.0
        cmovnz    %r9, %rbp                                     #18.0
        testq     %rsi, %rsi                                    #18.0
        cmovnz    %r14, %rbx                                    #18.0
        testq     %rsi, %rsi                                    #18.0
        cmovnz    %r13, %rdi                                    #18.0
        testq     %rsi, %rsi                                    #18.0
        cmovnz    %r12, %r10                                    #18.0
        movq      %rbp, 32(%rsp)                                #229.35
        movq      %rbx, 40(%rsp)                                #229.35
        movq      %rdi, 48(%rsp)                                #229.35
        movq      %r10, 56(%rsp)                                #229.35
        vmovups   %xmm0, 64(%rsp)                               #230.20
        vmovups   %xmm0, 80(%rsp)                               #230.20
        movq      240(%rsp), %rsi                               #53.32[spill]
        xorl      %r15d, %r15d                                  #53.32
        subq      %r10, %rsi                                    #53.32
        movl      %r15d, %r10d                                  #56.32
        sbbq      %rdi, %rcx                                    #54.32
        movq      $0xffffffff00000001, %r13                     #64.30
        movq      232(%rsp), %rdi                               #55.32[spill]
        sbbq      %rbx, %rdi                                    #55.32
        vpxor     %xmm0, %xmm0, %xmm0                           #240.21
        sbbq      %rbp, %r8                                     #56.32
        setb      %r10b                                         #56.32
        xorl      %r14d, %r14d                                  #56.32
        xorl      %r12d, %r12d                                  #56.32
        movq      $-1, %rbp                                     #56.32
        testq     %r10, %r10                                    #18.0
        cmovnz    %rbp, %r14                                    #18.0
        xorl      %r10d, %r10d                                  #59.32
        xorl      %ebx, %ebx                                    #59.32
        movl      %r14d, %r9d                                   #61.32
        adox      %r14, %rsi                                    #59.32
        movq      %rsi, 88(%rsp)                                #230.34
        adox      %r9, %rcx                                     #61.32
        movq      %rcx, 80(%rsp)                                #230.34
        adox      %r12, %rdi                                    #62.32
        movq      %rdi, 72(%rsp)                                #230.34
        seto      %r10b                                         #62.32
        xorl      %ebx, %ebx                                    #62.32
        andq      %r13, %r14                                    #64.30
        cmpl      %r10d, %r15d                                  #64.30
        adcx      %r14, %r8                                     #64.30
        xorl      %r10d, %r10d                                  #64.30
        movq      %r8, 64(%rsp)                                 #230.34
        subq      216(%rsp), %rsi                               #53.32[spill]
        sbbq      224(%rsp), %rcx                               #54.32[spill]
        sbbq      208(%rsp), %rdi                               #55.32[spill]
        sbbq      200(%rsp), %r8                                #56.32[spill]
        setb      %r10b                                         #56.32
        testq     %r10, %r10                                    #18.0
        cmovnz    %rbp, %rbx                                    #18.0
        xorl      %r10d, %r10d                                  #59.32
        movl      %ebx, %r10d                                   #61.32
        adox      %rbx, %rsi                                    #59.32
        adox      %r10, %rcx                                    #61.32
        movq      112(%rsp), %r10                               #66.1[spill]
        adox      %r12, %rdi                                    #62.32
        movl      %r15d, %r12d                                  #62.32
        movq      %rdi, 8(%r10)                                 #66.1
        seto      %r12b                                         #62.32
        andq      %rbx, %r13                                    #64.30
        cmpl      %r12d, %r15d                                  #64.30
        movq      104(%rsp), %r12                               #18.0[spill]
        adcx      %r13, %r8                                     #64.30
        movq      %rcx, 16(%r10)                                #67.1
        movq      %rsi, 24(%r10)                                #68.1
        movq      %r8, (%r10)                                   #65.1
        movq      24(%r12), %r9                                 #18.0
        movq      96(%rsp), %r13                                #18.0[spill]
        testq     %r13, %r13                                    #18.0
        cmovnz    %rsi, %r9                                     #18.0
        movq      %r9, 24(%r10)                                 #232.5
        movq      16(%r12), %rbx                                #18.0
        testq     %r13, %r13                                    #18.0
        cmovnz    %rcx, %rbx                                    #18.0
        movq      %rbx, 16(%r10)                                #233.5
        movq      8(%r12), %rbp                                 #18.0
        testq     %r13, %r13                                    #18.0
        cmovnz    %rdi, %rbp                                    #18.0
        movq      %rbp, 8(%r10)                                 #234.5
        movq      (%r12), %rcx                                  #18.0
        testq     %r13, %r13                                    #18.0
        cmovnz    %r8, %rcx                                     #18.0
        movq      120(%rsp), %rsi                               #18.0[spill]
        movq      %rcx, (%r10)                                  #235.5
        movq      128(%rsp), %rdi                               #18.0[spill]
        movq      24(%rsi), %r8                                 #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %r9, %r8                                      #18.0
        movq      %r8, 24(%r10)                                 #236.5
        movq      %r8, 144(%rsp)                                #18.0[spill]
        movq      16(%rsi), %r9                                 #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %rbx, %r9                                     #18.0
        movq      %r9, 16(%r10)                                 #237.5
        movq      %r9, 152(%rsp)                                #18.0[spill]
        movq      8(%rsi), %rbx                                 #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %rbp, %rbx                                    #18.0
        movq      %rbx, 8(%r10)                                 #238.5
        movq      %rbx, 160(%rsp)                               #18.0[spill]
        movq      (%rsi), %rbp                                  #18.0
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %rcx, %rbp                                    #18.0
        movq      %rbp, 248(%rsp)                               #18.0[spill]
        movq      %rbp, (%r10)                                  #239.5
        vmovups   %xmm0, (%rsp)                                 #240.21
        vmovups   %xmm0, 16(%rsp)                               #240.21
        movq      %rsi, %rbp                                    #72.34
        xorl      %r8d, %r8d                                    #76.32
        movq      %rdx, 88(%rsp)                                #[spill]
        xorl      %r9d, %r9d                                    #76.32
        movq      216(%rsp), %rdx                               #72.34[spill]
        movq      %rax, 232(%rsp)                               #[spill]
        mulx      56(%rbp), %rax, %rdi                          #72.34
        movq      $0x0ffffffff, %r13                            #81.34
        mulx      48(%rbp), %rbx, %r10                          #73.34
        movq      $0xffffffff00000001, %r14                     #82.34
        adox      %rbx, %rdi                                    #76.32
        vpxor     %xmm0, %xmm0, %xmm0                           #241.21
        movq      %r11, 80(%rsp)                                #[spill]
        mulx      40(%rbp), %rcx, %r11                          #74.34
        adox      %rcx, %r10                                    #77.32
        mulx      32(%rbp), %rsi, %r12                          #75.34
        movq      %rax, %rdx                                    #80.34
        adox      %rsi, %r11                                    #78.32
        movq      $-1, %rsi                                     #80.34
        seto      %r9b                                          #78.32
        clc                                                     #79.30
        adcx      %r12, %r9                                     #79.30
        mulx      %r13, %r12, %rcx                              #81.34
        mulx      %rsi, %r15, %rbx                              #80.34
        mulx      %r14, %r14, %r13                              #82.34
        movl      %r8d, %edx                                    #83.32
        adox      %r8d, %edx                                    #83.32
        movl      %r8d, %edx                                    #85.32
        adox      %r12, %rbx                                    #83.32
        movl      $0, %r12d                                     #84.32
        adox      %r12, %rcx                                    #84.32
        adox      %r12, %r14                                    #85.32
        seto      %dl                                           #85.32
        clc                                                     #86.30
        adcx      %r13, %rdx                                    #86.30
        movl      %r8d, %r13d                                   #87.30
        adox      %r8d, %r13d                                   #87.30
        adox      %r15, %rax                                    #87.30
        adox      %rbx, %rdi                                    #88.32
        movl      %r8d, %ebx                                    #91.32
        adox      %rcx, %r10                                    #89.32
        adox      %r14, %r11                                    #90.32
        adox      %rdx, %r9                                     #91.32
        movq      224(%rsp), %rdx                               #92.34[spill]
        seto      %bl                                           #91.32
        clc                                                     #96.32
        mulx      56(%rbp), %r15, %r14                          #92.34
        mulx      48(%rbp), %rcx, %r13                          #93.34
        adcx      %rcx, %r14                                    #96.32
        mulx      40(%rbp), %rax, %rcx                          #94.34
        adcx      %rax, %r13                                    #97.32
        mulx      32(%rbp), %rax, %rbp                          #95.34
        movl      %r8d, %edx                                    #99.30
        adcx      %rax, %rcx                                    #98.32
        movl      %r8d, %eax                                    #98.32
        setb      %al                                           #98.32
        adox      %r8d, %edx                                    #99.30
        adox      %rbp, %rax                                    #99.30
        movl      %r8d, %ebp                                    #99.30
        seto      %bpl                                          #99.30
        clc                                                     #100.34
        adcx      %r15, %rdi                                    #100.34
        movq      %rdi, %rdx                                    #105.36
        adcx      %r14, %r10                                    #101.34
        movq      $0xffffffff00000001, %r14                     #107.36
        adcx      %r13, %r11                                    #102.34
        mulx      %r14, %r13, %r14                              #107.36
        adcx      %rcx, %r9                                     #103.34
        movl      %r8d, %ecx                                    #104.34
        adcx      %rax, %rbx                                    #104.34
        mulx      %rsi, %rax, %rbp                              #105.36
        movq      $0x0ffffffff, %rsi                            #106.36
        mulx      %rsi, %r15, %rsi                              #106.36
        movl      %r8d, %edx                                    #108.34
        setb      %cl                                           #104.34
        adox      %r8d, %edx                                    #108.34
        movq      208(%rsp), %rdx                               #118.36[spill]
        adox      %r15, %rbp                                    #108.34
        movl      %r8d, %r15d                                   #110.34
        adox      %r12, %rsi                                    #109.34
        adox      %r12, %r13                                    #110.34
        seto      %r15b                                         #110.34
        clc                                                     #111.31
        adcx      %r14, %r15                                    #111.31
        movl      %r8d, %r14d                                   #112.31
        adox      %r8d, %r14d                                   #112.31
        adox      %rax, %rdi                                    #112.31
        movl      %r8d, %edi                                    #116.34
        adox      %rbp, %r10                                    #113.34
        adox      %rsi, %r11                                    #114.34
        adox      %r13, %r9                                     #115.34
        movq      120(%rsp), %r13                               #118.36[spill]
        adox      %r15, %rbx                                    #116.34
        mulx      56(%r13), %rax, %rbp                          #118.36
        seto      %dil                                          #116.34
        clc                                                     #122.34
        mulx      48(%r13), %rsi, %r15                          #119.36
        adcx      %rsi, %rbp                                    #122.34
        mulx      40(%r13), %r14, %rsi                          #120.36
        adcx      %r14, %r15                                    #123.34
        mulx      32(%r13), %r13, %r14                          #121.36
        movl      %r8d, %edx                                    #125.31
        adcx      %r13, %rsi                                    #124.34
        movl      %r8d, %r13d                                   #124.34
        setb      %r13b                                         #124.34
        adox      %r8d, %edx                                    #125.31
        adox      %r14, %r13                                    #125.31
        movl      %r8d, %r14d                                   #125.31
        seto      %r14b                                         #125.31
        clc                                                     #126.34
        adcx      %rax, %r10                                    #126.34
        movl      %r8d, %eax                                    #129.34
        movq      %r10, %rdx                                    #131.36
        adcx      %rbp, %r11                                    #127.34
        movq      $0x0ffffffff, %rbp                            #132.36
        mulx      %rbp, %rbp, %r14                              #132.36
        adcx      %r15, %r9                                     #128.34
        adcx      %rsi, %rbx                                    #129.34
        movq      $0xffffffff00000001, %rsi                     #133.36
        mulx      %rsi, %rsi, %r15                              #133.36
        setb      %al                                           #129.34
        addl      %edi, %ecx                                    #130.34
        movq      $-1, %rdi                                     #130.34
        cmpl      %eax, %r8d                                    #130.34
        movl      %r8d, %eax                                    #130.34
        adcx      %r13, %rcx                                    #130.34
        mulx      %rdi, %rdi, %r13                              #131.36
        movl      %r8d, %edx                                    #134.34
        setb      %al                                           #130.34
        adox      %r8d, %edx                                    #134.34
        movq      200(%rsp), %rdx                               #144.36[spill]
        adox      %rbp, %r13                                    #134.34
        movl      %r8d, %ebp                                    #136.34
        adox      %r12, %r14                                    #135.34
        adox      %r12, %rsi                                    #136.34
        seto      %bpl                                          #136.34
        clc                                                     #137.31
        adcx      %r15, %rbp                                    #137.31
        movl      %r8d, %r15d                                   #138.31
        adox      %r8d, %r15d                                   #138.31
        adox      %rdi, %r10                                    #138.31
        movl      %r8d, %r10d                                   #142.34
        adox      %r13, %r11                                    #139.34
        adox      %r14, %r9                                     #140.34
        adox      %rsi, %rbx                                    #141.34
        movq      120(%rsp), %rsi                               #144.36[spill]
        adox      %rbp, %rcx                                    #142.34
        mulx      56(%rsi), %rdi, %r13                          #144.36
        seto      %r10b                                         #142.34
        clc                                                     #148.34
        mulx      48(%rsi), %r14, %rbp                          #145.36
        adcx      %r14, %r13                                    #148.34
        mulx      40(%rsi), %r15, %r14                          #146.36
        adcx      %r15, %rbp                                    #149.34
        mulx      32(%rsi), %rsi, %r15                          #147.36
        movl      %r8d, %edx                                    #151.31
        adcx      %rsi, %r14                                    #150.34
        movl      %r8d, %esi                                    #150.34
        setb      %sil                                          #150.34
        adox      %r8d, %edx                                    #151.31
        adox      %r15, %rsi                                    #151.31
        movl      %r8d, %r15d                                   #151.31
        seto      %r15b                                         #151.31
        clc                                                     #152.34
        adcx      %rdi, %r11                                    #152.34
        movq      %r11, %rdx                                    #157.36
        adcx      %r13, %r9                                     #153.34
        movl      %r8d, %r13d                                   #155.34
        adcx      %rbp, %rbx                                    #154.34
        movq      $0x0ffffffff, %rbp                            #158.36
        mulx      %rbp, %rbp, %r15                              #158.36
        adcx      %r14, %rcx                                    #155.34
        setb      %r13b                                         #155.34
        xorl      %edi, %edi                                    #155.34
        addl      %r10d, %eax                                   #156.34
        movq      $-1, %r10                                     #156.34
        cmpl      %r13d, %r8d                                   #156.34
        movq      $0xffffffff00000001, %r13                     #159.36
        adcx      %rsi, %rax                                    #156.34
        mulx      %r10, %r10, %rsi                              #157.36
        mulx      %r13, %r13, %r14                              #159.36
        movl      %r8d, %edx                                    #160.34
        setb      %dil                                          #156.34
        adox      %r8d, %edx                                    #160.34
        adox      %rbp, %rsi                                    #160.34
        movl      %r8d, %ebp                                    #162.34
        adox      %r12, %r15                                    #161.34
        adox      %r12, %r13                                    #162.34
        seto      %bpl                                          #162.34
        clc                                                     #163.31
        adcx      %r14, %rbp                                    #163.31
        movl      %r8d, %r14d                                   #164.31
        adox      %r8d, %r14d                                   #164.31
        adox      %r10, %r11                                    #164.31
        movq      $0xffffffff00000001, %r10                     #173.34
        movl      %r8d, %r11d                                   #168.34
        adox      %rsi, %r9                                     #165.34
        movq      $0x0ffffffff, %rsi                            #171.34
        movq      %r9, %rdx                                     #170.34
        adox      %r15, %rbx                                    #166.34
        adox      %r13, %rcx                                    #167.34
        adox      %rbp, %rax                                    #168.34
        movq      %rax, %rbp                                    #173.34
        seto      %r11b                                         #168.34
        xorl      %r15d, %r15d                                  #168.34
        addl      %r11d, %edi                                   #174.31
        movq      $-1, %r11                                     #170.34
        subq      %r11, %rdx                                    #170.34
        movq      %rbx, %r11                                    #171.34
        sbbq      %rsi, %r11                                    #171.34
        movq      %rcx, %rsi                                    #172.34
        sbbq      %r12, %rsi                                    #172.34
        sbbq      %r10, %rbp                                    #173.34
        setb      %r15b                                         #173.34
        cmpl      %r15d, %r8d                                   #174.31
        sbbq      %r12, %rdi                                    #174.31
        setb      %r8b                                          #174.31
        testq     %r8, %r8                                      #18.0
        cmovnz    %rax, %rbp                                    #18.0
        testq     %r8, %r8                                      #18.0
        cmovnz    %rcx, %rsi                                    #18.0
        testq     %r8, %r8                                      #18.0
        cmovnz    %rbx, %r11                                    #18.0
        movq      %r11, 72(%rsp)                                #18.0[spill]
        testq     %r8, %r8                                      #18.0
        cmovnz    %r9, %rdx                                     #18.0
        movq      %rdx, 64(%rsp)                                #18.0[spill]
        movq      %rbp, (%rsp)                                  #240.34
        movq      %rsi, 8(%rsp)                                 #240.34
        movq      %r11, 16(%rsp)                                #240.34
        movq      %rdx, 24(%rsp)                                #240.34
        vmovups   %xmm0, 32(%rsp)                               #241.21
        vmovups   %xmm0, 48(%rsp)                               #241.21
        movq      80(%rsp), %r11                                #241.21[spill]
        movq      232(%rsp), %rax                               #241.21[spill]
        movq      88(%rsp), %rdx                                #241.21[spill]
        xorl      %ebx, %ebx                                    #53.32
        xorl      %edi, %edi                                    #53.32
        subq      144(%rsp), %rdx                               #53.32[spill]
        movq      136(%rsp), %rcx                               #56.32[spill]
        sbbq      152(%rsp), %rax                               #54.32[spill]
        sbbq      160(%rsp), %r11                               #55.32[spill]
        movq      $0xffffffff00000001, %r15                     #64.30
        sbbq      248(%rsp), %rcx                               #56.32[spill]
        vpxor     %xmm0, %xmm0, %xmm0                           #242.21
        setb      %dil                                          #56.32
        movq      $-1, %r8                                      #56.32
        xorl      %r13d, %r13d                                  #56.32
        xorl      %r14d, %r14d                                  #56.32
        testq     %rdi, %rdi                                    #18.0
        cmovnz    %r8, %r13                                     #18.0
        xorl      %r9d, %r9d                                    #59.32
        movl      %r13d, %r10d                                  #61.32
        adcx      %r13, %rdx                                    #59.32
        movq      %rdx, 56(%rsp)                                #241.34
        adcx      %r10, %rax                                    #61.32
        movq      %rax, 48(%rsp)                                #241.34
        adcx      %r12, %r11                                    #62.32
        movq      %r11, 40(%rsp)                                #241.34
        setb      %r14b                                         #62.32
        andq      %r13, %r15                                    #64.30
        cmpl      %r14d, %ebx                                   #64.30
        adcx      %r15, %rcx                                    #64.30
        movq      %rcx, 136(%rsp)                               #64.30[spill]
        movq      %rcx, 32(%rsp)                                #241.34
        vmovups   %xmm0, (%rsp)                                 #242.21
        vmovups   %xmm0, 16(%rsp)                               #242.21
        movq      %rsi, 32(%rsp)                                #[spill]
        movq      $0x0ffffffff, %r13                            #81.34
        xorl      %esi, %esi                                    #76.32
        movq      $0xffffffff00000001, %r12                     #82.34
        movq      168(%rsp), %r9                                #72.34[spill]
        mulx      184(%rsp), %rdi, %r10                         #73.34[spill]
        movq      %rbp, 40(%rsp)                                #[spill]
        mulx      %r9, %rbx, %rbp                               #72.34
        adox      %rdi, %rbp                                    #76.32
        movl      %esi, %edi                                    #78.32
        movq      %r11, 80(%rsp)                                #[spill]
        mulx      176(%rsp), %r8, %r11                          #74.34[spill]
        adox      %r8, %r10                                     #77.32
        mulx      192(%rsp), %rcx, %r15                         #75.34[spill]
        movq      %rbx, %rdx                                    #80.34
        adox      %rcx, %r11                                    #78.32
        movq      $-1, %rcx                                     #80.34
        seto      %dil                                          #78.32
        clc                                                     #79.30
        adcx      %r15, %rdi                                    #79.30
        mulx      %rcx, %r14, %r15                              #80.34
        mulx      %r13, %r8, %rcx                               #81.34
        mulx      %r12, %r13, %r12                              #82.34
        movl      %esi, %edx                                    #83.32
        adox      %esi, %edx                                    #83.32
        movl      %esi, %edx                                    #85.32
        adox      %r8, %r15                                     #83.32
        movl      $0, %r8d                                      #84.32
        adox      %r8, %rcx                                     #84.32
        adox      %r8, %r13                                     #85.32
        seto      %dl                                           #85.32
        clc                                                     #86.30
        adcx      %r12, %rdx                                    #86.30
        movl      %esi, %r12d                                   #87.30
        adox      %esi, %r12d                                   #87.30
        adox      %r14, %rbx                                    #87.30
        adox      %r15, %rbp                                    #88.32
        adox      %rcx, %r10                                    #89.32
        movl      %esi, %ecx                                    #91.32
        adox      %r13, %r11                                    #90.32
        adox      %rdx, %rdi                                    #91.32
        movq      %rax, %rdx                                    #92.34
        mulx      184(%rsp), %r15, %r13                         #93.34[spill]
        seto      %cl                                           #91.32
        clc                                                     #96.32
        mulx      %r9, %rbx, %r14                               #92.34
        adcx      %r15, %r14                                    #96.32
        mulx      176(%rsp), %r15, %r12                         #94.34[spill]
        adcx      %r15, %r13                                    #97.32
        mulx      192(%rsp), %r15, %rax                         #95.34[spill]
        movl      %esi, %edx                                    #99.30
        adcx      %r15, %r12                                    #98.32
        movl      %esi, %r15d                                   #98.32
        setb      %r15b                                         #98.32
        adox      %esi, %edx                                    #99.30
        adox      %rax, %r15                                    #99.30
        clc                                                     #100.34
        movq      $0x0ffffffff, %rax                            #106.36
        adcx      %rbx, %rbp                                    #100.34
        movl      %esi, %ebx                                    #104.34
        movq      %rbp, %rdx                                    #105.36
        adcx      %r14, %r10                                    #101.34
        movq      $-1, %r14                                     #105.36
        adcx      %r13, %r11                                    #102.34
        mulx      %rax, %r13, %rax                              #106.36
        adcx      %r12, %rdi                                    #103.34
        adcx      %r15, %rcx                                    #104.34
        setb      %bl                                           #104.34
        movl      %ebx, 48(%rsp)                                #104.34[spill]
        mulx      %r14, %r15, %rbx                              #105.36
        movq      $0xffffffff00000001, %r14                     #107.36
        mulx      %r14, %r14, %r12                              #107.36
        movl      %esi, %edx                                    #108.34
        adox      %esi, %edx                                    #108.34
        movq      80(%rsp), %rdx                                #118.36[spill]
        adox      %r13, %rbx                                    #108.34
        movl      %esi, %r13d                                   #110.34
        adox      %r8, %rax                                     #109.34
        adox      %r8, %r14                                     #110.34
        seto      %r13b                                         #110.34
        clc                                                     #111.31
        adcx      %r12, %r13                                    #111.31
        movl      %esi, %r12d                                   #112.31
        adox      %esi, %r12d                                   #112.31
        movl      %esi, %r12d                                   #116.34
        adox      %r15, %rbp                                    #112.31
        adox      %rbx, %r10                                    #113.34
        adox      %rax, %r11                                    #114.34
        adox      %r14, %rdi                                    #115.34
        mulx      184(%rsp), %rbx, %r14                         #119.36[spill]
        adox      %r13, %rcx                                    #116.34
        mulx      %r9, %r13, %rbp                               #118.36
        seto      %r12b                                         #116.34
        clc                                                     #122.34
        adcx      %rbx, %rbp                                    #122.34
        mulx      176(%rsp), %r15, %rbx                         #120.36[spill]
        adcx      %r15, %r14                                    #123.34
        mulx      192(%rsp), %r15, %rax                         #121.36[spill]
        movl      %esi, %edx                                    #125.31
        adcx      %r15, %rbx                                    #124.34
        movl      %esi, %r15d                                   #124.34
        setb      %r15b                                         #124.34
        adox      %esi, %edx                                    #125.31
        adox      %rax, %r15                                    #125.31
        clc                                                     #126.34
        movl      48(%rsp), %eax                                #130.34[spill]
        adcx      %r13, %r10                                    #126.34
        movq      $0x0ffffffff, %r13                            #132.36
        movq      %r10, %rdx                                    #131.36
        adcx      %rbp, %r11                                    #127.34
        movl      %esi, %ebp                                    #129.34
        adcx      %r14, %rdi                                    #128.34
        movq      $0xffffffff00000001, %r14                     #133.36
        adcx      %rbx, %rcx                                    #129.34
        setb      %bpl                                          #129.34
        xorl      %ebx, %ebx                                    #129.34
        addl      %r12d, %eax                                   #130.34
        cmpl      %ebp, %esi                                    #130.34
        movq      $-1, %rbp                                     #131.36
        mulx      %r14, %r14, %r12                              #133.36
        adcx      %r15, %rax                                    #130.34
        setb      %bl                                           #130.34
        movl      %ebx, 56(%rsp)                                #130.34[spill]
        mulx      %rbp, %r15, %rbx                              #131.36
        mulx      %r13, %r13, %rbp                              #132.36
        movl      %esi, %edx                                    #134.34
        adox      %esi, %edx                                    #134.34
        movq      136(%rsp), %rdx                               #144.36[spill]
        adox      %r13, %rbx                                    #134.34
        movl      %esi, %r13d                                   #136.34
        adox      %r8, %rbp                                     #135.34
        adox      %r8, %r14                                     #136.34
        seto      %r13b                                         #136.34
        clc                                                     #137.31
        adcx      %r12, %r13                                    #137.31
        movl      %esi, %r12d                                   #138.31
        adox      %esi, %r12d                                   #138.31
        movl      %esi, %r12d                                   #151.31
        adox      %r15, %r10                                    #138.31
        adox      %rbx, %r11                                    #139.34
        mulx      184(%rsp), %r10, %rbx                         #145.36[spill]
        adox      %rbp, %rdi                                    #140.34
        adox      %r14, %rcx                                    #141.34
        movl      %esi, %r14d                                   #142.34
        adox      %r13, %rax                                    #142.34
        mulx      %r9, %r9, %r13                                #144.36
        seto      %r14b                                         #142.34
        clc                                                     #148.34
        adcx      %r10, %r13                                    #148.34
        mulx      176(%rsp), %r15, %r10                         #146.36[spill]
        adcx      %r15, %rbx                                    #149.34
        mulx      192(%rsp), %r15, %rbp                         #147.36[spill]
        adcx      %r15, %r10                                    #150.34
        movl      %esi, %r15d                                   #150.34
        setb      %r15b                                         #150.34
        adox      %esi, %r12d                                   #151.31
        adox      %rbp, %r15                                    #151.31
        clc                                                     #152.34
        movl      56(%rsp), %ebp                                #156.34[spill]
        adcx      %r9, %r11                                     #152.34
        movl      %esi, %r9d                                    #155.34
        movq      %r11, %rdx                                    #157.36
        adcx      %r13, %rdi                                    #153.34
        movq      $0xffffffff00000001, %r13                     #159.36
        mulx      %r13, %r13, %r12                              #159.36
        adcx      %rbx, %rcx                                    #154.34
        adcx      %r10, %rax                                    #155.34
        movq      $-1, %r10                                     #157.36
        mulx      %r10, %rbx, %r10                              #157.36
        setb      %r9b                                          #155.34
        addl      %r14d, %ebp                                   #156.34
        cmpl      %r9d, %esi                                    #156.34
        movq      $0x0ffffffff, %r9                             #158.36
        mulx      %r9, %r14, %r9                                #158.36
        movl      %esi, %edx                                    #160.34
        adcx      %r15, %rbp                                    #156.34
        movl      %esi, %r15d                                   #156.34
        setb      %r15b                                         #156.34
        adox      %esi, %edx                                    #160.34
        adox      %r14, %r10                                    #160.34
        movl      %esi, %r14d                                   #162.34
        adox      %r8, %r9                                      #161.34
        adox      %r8, %r13                                     #162.34
        seto      %r14b                                         #162.34
        clc                                                     #163.31
        adcx      %r12, %r14                                    #163.31
        movl      %esi, %r12d                                   #164.31
        adox      %esi, %r12d                                   #164.31
        adox      %rbx, %r11                                    #164.31
        movl      %esi, %r11d                                   #168.34
        adox      %r10, %rdi                                    #165.34
        movq      $0x0ffffffff, %r10                            #171.34
        adox      %r9, %rcx                                     #166.34
        movq      %rdi, %r9                                     #170.34
        movq      %rcx, %rbx                                    #171.34
        adox      %r13, %rax                                    #167.34
        adox      %r14, %rbp                                    #168.34
        seto      %r11b                                         #168.34
        movq      $-1, %rdx                                     #168.34
        xorl      %r12d, %r12d                                  #168.34
        xorl      %r13d, %r13d                                  #168.34
        addl      %r11d, %r15d                                  #174.31
        subq      %rdx, %r9                                     #170.34
        movq      %rbp, %rdx                                    #173.34
        movq      $0xffffffff00000001, %r11                     #173.34
        sbbq      %r10, %rbx                                    #171.34
        movq      %rax, %r10                                    #172.34
        sbbq      %r8, %r10                                     #172.34
        sbbq      %r11, %rdx                                    #173.34
        setb      %r13b                                         #173.34
        cmpl      %r13d, %esi                                   #174.31
        sbbq      %r8, %r15                                     #174.31
        setb      %r12b                                         #174.31
        testq     %r12, %r12                                    #18.0
        cmovnz    %rbp, %rdx                                    #18.0
        xorl      %ebp, %ebp                                    #18.0
        testq     %r12, %r12                                    #18.0
        cmovnz    %rax, %r10                                    #18.0
        testq     %r12, %r12                                    #18.0
        cmovnz    %rcx, %rbx                                    #18.0
        xorl      %ecx, %ecx                                    #56.32
        testq     %r12, %r12                                    #18.0
        cmovnz    %rdi, %r9                                     #18.0
        movq      $-1, %rdi                                     #18.0
        movq      %r9, 24(%rsp)                                 #242.34
        subq      64(%rsp), %r9                                 #53.32[spill]
        movq      %rbx, 16(%rsp)                                #242.34
        sbbq      72(%rsp), %rbx                                #54.32[spill]
        movq      %r10, 8(%rsp)                                 #242.34
        sbbq      32(%rsp), %r10                                #55.32[spill]
        movq      %rdx, (%rsp)                                  #242.34
        sbbq      40(%rsp), %rdx                                #56.32[spill]
        setb      %cl                                           #56.32
        testq     %rcx, %rcx                                    #18.0
        cmovnz    %rdi, %rbp                                    #18.0
        xorl      %eax, %eax                                    #59.32
        movl      %ebp, %r14d                                   #61.32
        adcx      %rbp, %r9                                     #59.32
        movq      96(%rsp), %rcx                                #18.0[spill]
        adcx      %r14, %rbx                                    #61.32
        adcx      %r8, %r10                                     #62.32
        movq      112(%rsp), %r8                                #66.1[spill]
        setb      %al                                           #62.32
        andq      %rbp, %r11                                    #64.30
        cmpl      %eax, %esi                                    #64.30
        movq      104(%rsp), %rax                               #18.0[spill]
        adcx      %r11, %rdx                                    #64.30
        movq      %r10, 40(%r8)                                 #66.1
        movq      %rbx, 48(%r8)                                 #67.1
        movq      %r9, 56(%r8)                                  #68.1
        movq      %rdx, 32(%r8)                                 #65.1
        movq      56(%rax), %rbp                                #18.0
        testq     %rcx, %rcx                                    #18.0
        cmovnz    %r9, %rbp                                     #18.0
        movq      %rbp, 56(%r8)                                 #244.5
        movq      48(%rax), %rdi                                #18.0
        testq     %rcx, %rcx                                    #18.0
        cmovnz    %rbx, %rdi                                    #18.0
        movq      %rdi, 48(%r8)                                 #245.5
        movq      40(%rax), %rbx                                #18.0
        testq     %rcx, %rcx                                    #18.0
        cmovnz    %r10, %rbx                                    #18.0
        movq      %rbx, 40(%r8)                                 #246.5
        movq      32(%rax), %r12                                #18.0
        testq     %rcx, %rcx                                    #18.0
        cmovnz    %rdx, %r12                                    #18.0
        movq      120(%rsp), %rsi                               #18.0[spill]
        movq      %r12, 32(%r8)                                 #247.5
        movq      128(%rsp), %r11                               #18.0[spill]
        movq      56(%rsi), %rdx                                #18.0
        testq     %r11, %r11                                    #18.0
        cmovnz    %rbp, %rdx                                    #18.0
        movq      %rdx, 56(%r8)                                 #18.0
        movq      48(%rsi), %r10                                #18.0
        testq     %r11, %r11                                    #18.0
        cmovnz    %rdi, %r10                                    #18.0
        movq      %r10, 48(%r8)                                 #18.0
        movq      40(%rsi), %r9                                 #18.0
        testq     %r11, %r11                                    #18.0
        cmovnz    %rbx, %r9                                     #18.0
        movq      %r9, 40(%r8)                                  #18.0
        movq      32(%rsi), %r13                                #18.0
        testq     %r11, %r11                                    #18.0
        cmovnz    %r12, %r13                                    #18.0
        movq      %r13, 32(%r8)                                 #18.0
        addq      $280, %rsp                                    #252.1
        popq      %rbp                                          #252.1
        popq      %rbx                                          #252.1
        popq      %r15                                          #252.1
        popq      %r14                                          #252.1
        popq      %r13                                          #252.1
        popq      %r12                                          #252.1
        ret                                                     #252.1
