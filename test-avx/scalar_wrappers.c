#include "gen_scalar_add.c"
#include "gen_scalar_carry.c"

void scalar_add4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]) {
    fiat_25519_add(out+0,a+0,b+0); fiat_25519_add(out+5,a+5,b+5);
    fiat_25519_add(out+10,a+10,b+10); fiat_25519_add(out+15,a+15,b+15);
}
void scalar_sub4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]) {
    static const uint64_t bal[5]={0xfffffffffffda,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe};
    for(int j=0;j<4;j++) for(int k=0;k<5;k++) out[j*5+k]=bal[k]+a[j*5+k]-b[j*5+k];
}
void scalar_opp4(uint64_t out[20], const uint64_t a[20]) {
    static const uint64_t bal[5]={0xfffffffffffda,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe};
    for(int j=0;j<4;j++) for(int k=0;k<5;k++) out[j*5+k]=bal[k]-a[j*5+k];
}
void scalar_carry4(uint64_t out[20], const uint64_t a[20]) {
    fiat_25519_carry(out+0,a+0); fiat_25519_carry(out+5,a+5);
    fiat_25519_carry(out+10,a+10); fiat_25519_carry(out+15,a+15);
}
void scalar_carry_add4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]) {
    uint64_t tmp[20];
    fiat_25519_add(tmp+0,a+0,b+0); fiat_25519_add(tmp+5,a+5,b+5);
    fiat_25519_add(tmp+10,a+10,b+10); fiat_25519_add(tmp+15,a+15,b+15);
    fiat_25519_carry(out+0,tmp+0); fiat_25519_carry(out+5,tmp+5);
    fiat_25519_carry(out+10,tmp+10); fiat_25519_carry(out+15,tmp+15);
}
void scalar_carry_sub4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]) {
    static const uint64_t bal[5]={0xfffffffffffda,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe};
    uint64_t tmp[20];
    for(int j=0;j<4;j++) for(int k=0;k<5;k++) tmp[j*5+k]=bal[k]+a[j*5+k]-b[j*5+k];
    fiat_25519_carry(out+0,tmp+0); fiat_25519_carry(out+5,tmp+5);
    fiat_25519_carry(out+10,tmp+10); fiat_25519_carry(out+15,tmp+15);
}
void scalar_carry_opp4(uint64_t out[20], const uint64_t a[20]) {
    static const uint64_t bal[5]={0xfffffffffffda,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe,0xffffffffffffe};
    uint64_t tmp[20];
    for(int j=0;j<4;j++) for(int k=0;k<5;k++) tmp[j*5+k]=bal[k]-a[j*5+k];
    fiat_25519_carry(out+0,tmp+0); fiat_25519_carry(out+5,tmp+5);
    fiat_25519_carry(out+10,tmp+10); fiat_25519_carry(out+15,tmp+15);
}
