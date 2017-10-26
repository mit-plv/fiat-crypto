q = 2**255-19
modulus_bytes = 32
a24 = 0x01db41

def ladderstep(x1, x, z, x_p, z_p):
  origx = x			
  x = (x + z)%q		
  z = (origx - z)%q		
  origx_p = x_p			
  x_p = (x_p + z_p)%q		
  z_p = (origx_p - z_p)%q	
  xx_p = (x_p * z)%q		
  zz_p = (x * z_p)%q		
  origx_p = xx_p			
  xx_p = (xx_p + zz_p)%q		
  zz_p = (origx_p - zz_p)%q	
  x3 = (xx_p*xx_p)%q		
  zzz_p = (zz_p*zz_p)%q		
  z3 = (zzz_p * x1)%q		
  xx = (x*x)%q			
  zz = (z*z)%q			
  x2 = (xx * zz)%q		
  zz = (xx - zz)%q		
  zzz = (zz * a24)%q		
  zzz = (zzz + xx)%q		
  z2 = (zz * zzz)%q		
  return ((x2, z2), (x3, z3))

def crypto_scalarmult(secret, secretbits, point):
  x1 = sum(point[i] << (8*i) for i in range(modulus_bytes))
  x = 1; z = 0; x_p = x1; z_p = 1;
  swap = 0

  i = secretbits - 1
  while i >= 0:
    bit = secret[i//8] >> (i%8)&1
    # print(bit, x*pow(z,q-2,q)%q, x_p*pow(z_p,q-2,q)%q)
    if swap ^ bit: ((x, z), (x_p, z_p)) = ((x_p, z_p), (x, z))
    swap = bit
    (x, z), (x_p, z_p) = ladderstep(x1, x, z, x_p, z_p)
    i -= 1
  if swap: ((x, z), (x_p, z_p)) = ((x_p, z_p), (x, z))
  x = (x*pow(z,q-2,q))%q
  return [((x >> (8*i)) & 0xff) for i in range(32)]

if __name__ == '__main__':
  BASE = [9]+31*[0]
  assert crypto_scalarmult([1]+31*[0], 256, BASE) == BASE

  a = [1] + 31*[0]
  for _ in range(200):
    a[0] &= 248
    a[31] &= 127
    a[31] |= 64
    a = crypto_scalarmult(a, 256, BASE)
  assert a == [137, 22, 31, 222, 136, 123, 43, 83, 222, 84, 154, 244, 131, 148, 1, 6, 236, 193, 20, 214, 152, 45, 170, 152, 37, 109, 226, 59, 223, 119, 102, 26]
