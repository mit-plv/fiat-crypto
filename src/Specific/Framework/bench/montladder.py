#!/usr/bin/env python
import sys, re

q = 2**448 - 2**224 - 1
modulus_bytes = 56
a24 = 39081

def eval_numexpr(numexpr):
  # copying from https://stackoverflow.com/a/25437733/377022
  numexpr = re.sub(r"\.(?![0-9])", "", numexpr) # purge any instance of '.' not followed by a number
  return eval(numexpr, {'__builtins__':None})

def usage(args, updates, retcode=0):
  print('USAGE: %s %s' % (args[0], ' '.join('[-D%s=NUMEXPR]' % k for k, v in updates)))
  sys.exit(retcode)

def update_defaults(args):
  global q
  global modulus_bytes
  global a24
  updates = (('q',q), ('modulus_bytes',modulus_bytes), ('a24',a24))
  if '--help' in args or '-h' in args: usage(args, updates)
  updates = dict(updates)
  found = []
  for k in updates.keys():
    for arg in args[1:]:
      if arg.startswith('-D%s=' % k):
        found.append(arg)
        updates[k] = eval_numexpr(arg[len('-D%s=' % k):])
      elif arg.startswith('-D%s' % k):
        found.append(arg)
        updates[k] = eval_numexpr(arg[len('-D%s' % k):])
  unfound = [arg for arg in args[1:] if arg not in found]
  if len(unfound) > 0:
    print('ERROR: unrecognized arguments: ' + ' '.join(map(repr, unfound)))
    usage(args, updates, retcode=1)
  q = updates['q']
  modulus_bytes = updates['modulus_bytes']
  a24 = updates['a24']
  print('q: %(q)s, modulus_bytes: %(modulus_bytes)s, a24: %(a24)s' % updates)

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
  return [((x >> (8*i)) & 0xff) for i in range(modulus_bytes)]

if __name__ == '__main__':
  update_defaults(sys.argv)
  BASE = [5]+(modulus_bytes-1)*[0]
  print (crypto_scalarmult([1]+(modulus_bytes-1)*[0], 8*modulus_bytes, BASE))

  s = [61, 38, 47, 221, 249, 236, 142, 136, 73, 82, 102, 254, 161, 154, 52, 210, 136, 130, 172, 239, 4, 81, 4, 208, 209, 170, 225, 33, 112, 10, 119, 156, 152, 76, 36, 248, 205, 215, 143, 191, 244, 73, 67, 235, 163, 104, 245, 75, 41, 37, 154, 79, 28, 96, 10, 211]
  s[0] &= 252
  s[55] |= 128

  P = [6, 252, 230, 64, 250, 52, 135, 191, 218, 95, 108, 242, 213, 38, 63, 138, 173, 136, 51, 76, 189, 7, 67, 127, 2, 15, 8, 249, 129, 77, 192, 49, 221, 189, 195, 140, 25, 198, 218, 37, 131, 250, 84, 41, 219, 148, 173, 161, 138, 167, 167, 251, 78, 248, 160, 134]
  Q = crypto_scalarmult(s, 8*modulus_bytes, P)
  print(''.join(hex(i)[2:] for i in Q))
  print(Q==[206, 62, 79, 249, 90, 96, 220, 102, 151, 218, 29, 177, 216, 94, 106, 251, 223, 121, 181, 10, 36, 18, 215, 84, 109, 95, 35, 159, 225, 79, 186, 173, 235, 68, 95, 198, 106, 1, 176, 119, 157, 152, 34, 57, 97, 17, 30, 33, 118, 98, 130, 247, 61, 217, 107, 111])
