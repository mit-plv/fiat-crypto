import socket, sys
from cryptography.hazmat.primitives.asymmetric import x25519

b = bool(int(sys.argv[1]))

# x25519.X25519PrivateKey.generate()
sk = x25519.X25519PrivateKey.from_private_bytes(
        b'P\x9d\xfb\x9bl\x044\xb9lv\x81\x13\xf0I8%\x99CO5.<>C\xa2\xbbH\t\xe42\xd1N')
print (', '.join("0x%02x"%b for b in sk.public_key()._raw_public_bytes()))

s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.settimeout(1000.0)
s.sendto(b'\x01\x00' + b'A'*32, ('10.55.55.3', 1823))

try:
    data, remote = s.recvfrom(2048)
    print('pk:', data[2:][:32])
    assert len(data) >= 2+32
    pk = x25519.X25519PublicKey.from_public_bytes(data[2:][:32])
    ss = sk.exchange(pk)
    print('ss:', ss)
    s.sendto(b'\x02\x00'+(ss[:16], ss[16:])[b], ('10.55.55.3', 1823))
except socket.timeout:
    print('REQUEST TIMED OUT')
