#include <unistd.h>
#include <stdio.h>

// cpucycles_amd64cpuinfo
long long cpucycles(void)
{
  unsigned long long result;
  asm volatile(".byte 15;.byte 49;shlq $32,%%rdx;orq %%rdx,%%rax"
    : "=a" (result) ::  "%rdx");
  return result;
}

static const long long usecs = 100*1000;

int main() {
  long long t0 = cpucycles();
  usleep(usecs);
  long long t1 = cpucycles();
  const long long tsc_hz  = ((t1-t0)*1000*1000)/usecs;
  const long long tsc_mhz = tsc_hz / 1000 / 1000;
  const long long tsc_ghz = tsc_mhz / 1000;
  printf("%1lli.%02lli\n", tsc_ghz, (tsc_mhz - 1000*tsc_ghz + 5)/10);
}
