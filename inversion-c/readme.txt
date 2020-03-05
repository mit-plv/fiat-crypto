inversion.c contains an implementation of inversion modulo p. To
change the prime modulus (or wordsize), compile montgomery_inversion.v
in src/ExtractionOCaml/, compile the extracted .ml and call the binary
as, e.g.,

./montgomery_inversion test '2^414 - 17' 64 > ../../inversion-c/montgomery_inversion.c

where you change '2^414 - 17' with your desired prime and 64 with your
desired wordsize. You also need to change a few values in inversion.c
(see the file). Note that if you use a curve description different
from 'test' then you have to change inversion.c accordingly.
