
#include <string.h>
#include <stdint.h>
#include "p256.h"

int main() {

{
uint64_t out[12] = {0};
uint64_t J[12] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb6c57b7b47ebaa2aL, 0x2e01a1c78240f1e9L, 0xdffebf812925c6e9L, 0x2205025c823b79d4L, 0xb914f2abe5ecd016L, 0x9d807c66950c0b1eL, 0xb145f8d2f7aa88a5L, 0xc3cbe3c3fd449c2fL, 0xe76fa0885ac8aa3aL, 0x86048cd4889ddaefL, 0x8a456a04a01249feL, 0x8618cf2be756ebc3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 1;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0xd07631bf24bc178cL, 0xa6bbd328e6963682L, 0xd0aa8b2826e0eba2L, 0xd6ddfce1cb10be7eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x26986032eae57400L, 0x8ca22de38df6eb0eL, 0x1161d3c87958b751L, 0x6503563390e10442L, 0x70b81487b6e6f344L, 0xccb3cca2b4c1fd02L, 0xbfde22211cb4e8e0L, 0x394bf032ee10a6edL, 0xe76fa0885ac8aa3aL, 0x86048cd4889ddaefL, 0x8a456a04a01249feL, 0x8618cf2be756ebc3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 2;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x62417dda94dd5719L, 0xe7edccaddd889441L, 0xd6ea57f17fb6d805L, 0xe79cc35062a450f0L, 0x2b8ff8c52c42ec2aL, 0x97443446e90f992cL, 0x5a55c721d0cf22e6L, 0xef929abe74aab054L, 0x1fffffffdL, 0xffffffffffffffffL, 0xfffffffe00000000L, 0x2L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb15edefefaea8a5eL, 0x806871e0903c7a77L, 0xffafe01d4971ba48L, 0x814097208ede752dL, 0x29e5593dd9a02bc9L, 0xf8cd2a18163d62L, 0x8bf1a47d55114b87L, 0x97c787fa89385f72L, 0x3b7d0449d64551cdL, 0x302466a444eed77cL, 0x522b501e00924ff4L, 0x30c6795f3ab75e1fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 3;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x62417dda94dd5719L, 0xe7edccaddd889441L, 0xd6ea57f17fb6d805L, 0xe79cc35062a450f0L, 0x2b8ff8c52c42ec2aL, 0x97443446e90f992cL, 0x5a55c721d0cf22e6L, 0xef929abe74aab054L, 0x1fffffffdL, 0xffffffffffffffffL, 0xfffffffe00000000L, 0x2L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0xd07631bf24bc178cL, 0xa6bbd328e6963682L, 0xd0aa8b2826e0eba2L, 0xd6ddfce1cb10be7eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa6180cc3b95d001aL, 0x288b78e37dbac384L, 0x5874f215562dd459L, 0x40d58ce438411089L, 0x7029104ecde688b8L, 0x6799456983fa057fL, 0xbc44415869d1c072L, 0x97e065dc214ddae1L, 0x3b7d0449d64551cdL, 0x302466a444eed77cL, 0x522b501e00924ff4L, 0x30c6795f3ab75e1fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 4;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0x7c4e71ffda1f43a1L, 0xca2166b8cb4e4be9L, 0x7aaba6c5c8f8a2e9L, 0x491018f1a77a0c09L, 0x1fffffffdL, 0xffffffffffffffffL, 0xfffffffe00000000L, 0x2L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 5;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0xd07631bf24bc178cL, 0xa6bbd328e6963682L, 0xd0aa8b2826e0eba2L, 0xd6ddfce1cb10be7eL, 0xfffffffe00000002L, 0x0L, 0x1ffffffffL, 0xfffffffffffffffeL};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 6;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0xd07631bf24bc178cL, 0xa6bbd328e6963682L, 0xd0aa8b2826e0eba2L, 0xd6ddfce1cb10be7eL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x26986032eae57400L, 0x8ca22de38df6eb0eL, 0x1161d3c87958b751L, 0x6503563390e10442L, 0x8f47eb7749190cbcL, 0x334c335d4b3e02fdL, 0x4021dddfe34b171fL, 0xc6b40fcd11ef5912L, 0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 7;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L, 0xfffffffe00000002L, 0x0L, 0x1ffffffffL, 0xfffffffffffffffeL};
uint64_t A[8] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x26986032eae57400L, 0x8ca22de38df6eb0eL, 0x1161d3c87958b751L, 0x6503563390e10442L, 0x70b81487b6e6f344L, 0xccb3cca2b4c1fd02L, 0xbfde22211cb4e8e0L, 0x394bf032ee10a6edL, 0xe76fa0885ac8aa3aL, 0x86048cd4889ddaefL, 0x8a456a04a01249feL, 0x8618cf2be756ebc3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 8;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x1eeb691fe11496dL, 0xffffffffffffffffL, 0xfe11496e00000000L, 0x1eeb692L, 0xf051a3410fae5d28L, 0x69L, 0xfae5d27ffffffffL, 0xffffff96f051a2d8L, 0x0L, 0x0L, 0x0L, 0x0L};
uint64_t A[8] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL};
// maybe A nz, maybe neither
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 9;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
// J nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 10;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0xd07631bf24bc178cL, 0xa6bbd328e6963682L, 0xd0aa8b2826e0eba2L, 0xd6ddfce1cb10be7eL, 0xfffffffe00000002L, 0x0L, 0x1ffffffffL, 0xfffffffffffffffeL};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
// J nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x0L, 0x0L, 0x0L, 0x0L, 0xd07631bf24bc178cL, 0xa6bbd328e6963682L, 0xd0aa8b2826e0eba2L, 0xd6ddfce1cb10be7eL, 0xfffffffe00000002L, 0x0L, 0x1ffffffffL, 0xfffffffffffffffeL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 11;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
// J nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 12;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xfe545c282897c3fcL, 0xb8842277752c41acL, 0x68363aba25e1a16eL, 0xfea912baa5659ae8L, 0xf720ee256d12597bL, 0x85665e9be39508c1L, 0x5806244afba977c5L, 0x2d36e9e7dc4c696bL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x1ba8b23c4e7b61dbL, 0x5c75422a3bfb505fL, 0x8392266f548267c2L, 0x1ab50760698fd966L, 0x7bd5f0f8bbc0113dL, 0x53a1e0762bce6c11L, 0x24a9b30477cbf81bL, 0xb03895250a03707dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x909e6b5eedddaa00L, 0xed6dacaccc0c21cdL, 0x6f49946256f07daeL, 0x626899b2567abb5eL, 0x1ee00ce4102f10f3L, 0x1c27c8095829ff4eL, 0xd2b5d6a46ca5cc54L, 0x4ec8af5dbce3c97aL, 0x1d54561325e39ddfL, 0xa3f11fb2c6cf0eb3L, 0x1b5bebb62ea0c653L, 0x1c0bf4a5c42a3e7dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 13;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8a4e72b69918062eL, 0x19d16caaf24441fL, 0xa9191c3f62abc039L, 0xe03d9ea371d75d7aL, 0xf0a27802fc75540dL, 0x3357b1746c40b10eL, 0xd703d3761a3abce9L, 0x40a4962357c25793L, 0x51cafe8fae35016L, 0xffffffffffffffffL, 0xfae3501700000000L, 0x51cafe9L};
uint64_t A[8] = {0x3355a9e2ed6f3d70L, 0xbb8ca626fa2e83a3L, 0x7633a743c1abf15fL, 0x62f6040fe8d14b9aL, 0x5482d45c245c0ed3L, 0xae880bfb66d033f9L, 0x15ecac2d10544c31L, 0xda782cbf9fd78f6dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x89094a89b1ca2c32L, 0xfc95c491beb09f34L, 0xed641c5d8fcf4247L, 0x4a43fe0aec8740f6L, 0x2db70e5f72bd0bc3L, 0x33e3545e5a2a8160L, 0x7ff91f499094eee0L, 0xa5738b43f7fbf8cfL, 0x4a126112307e48fL, 0x6312ca49df162cfcL, 0xe9561c542f11749L, 0x34371c89fada1fa1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 14;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd252887a9c73dbbeL, 0x76a92c282bdf98aL, 0xecb37b59e9ce7739L, 0xb6b30b9312888ebdL, 0x35571219b5a90736L, 0x7b2667b3a652b683L, 0xe6a617a2438e5749L, 0xafde8d892dc6a267L, 0x11ffffffedL, 0xffffffffffffffffL, 0xffffffee00000000L, 0x12L};
uint64_t A[8] = {0x633882d09d70b2fL, 0x751a305fb9992f1dL, 0x7e062c54bcd8ace8L, 0x52ebbfcdf7150d28L, 0xc9a8d89c7d00571eL, 0x6688e25bf90134ecL, 0xb8c44a8ed98d1f32L, 0x404354ed7f4ab63fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8d501b389d30d80cL, 0xce5b1b355c5bd487L, 0xfe76995f21e8f91bL, 0xa4772839503ddf47L, 0x79455c7e418c125bL, 0x6b5c7d79669a84ccL, 0x66ba1b42424d37d9L, 0x5738433a8b2b8c7fL, 0x7c28a9e72ad15d49L, 0x371fb30ef85dcc1aL, 0x58033d9db79eaa92L, 0x3212bbcd89f9ae74L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 15;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xb1a859fc16c815c9L, 0x3961fa381d4deebdL, 0x20ff6e31c49b7151L, 0x669195630ceab113L, 0x1c79a3f583d09f88L, 0xb1f73799092932caL, 0x962b66466f9c655L, 0x87c5624240d3a943L, 0x23ffffffdbfL, 0xffffffffffffffffL, 0xfffffdc000000000L, 0x240L};
uint64_t A[8] = {0xfd10d4229c2a4473L, 0xd255f5c688011591L, 0x6168ae5f30b59dfaL, 0x6f939d68a2be35f5L, 0xc9594125c2f30c3dL, 0xfaa6fa91bc6665c6L, 0xc1cbfb07ec4e60e8L, 0x5f41d10cb649b4c6L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3645fa3cb0530d73L, 0x1dc0d79b4caf0bebL, 0xb4a67397e2b9b540L, 0xdc354e678b1b0cL, 0x728270df643bcef5L, 0xf6d58cb76db7584eL, 0x2fea447f873d989L, 0xb872b51d19e3571bL, 0xaab2ec6069d44442L, 0x6cf22e17bca062d7L, 0xea4c52a11adff646L, 0x344d9fc195e82760L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 16;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd81f96e2d7477c21L, 0x6314732f676c6e33L, 0x48de527d7fe4b8a8L, 0x502dbfefa7b219afL, 0x9154d6bc5d4f5d9eL, 0x95ef90ba825e9baL, 0xa07772416e286a06L, 0xb9ed4c3a74e2164dL, 0xdcfa691f230596dfL, 0xffffffffffffffffL, 0x230596e000000000L, 0xdcfa6920L};
uint64_t A[8] = {0x316af5adbef1bf81L, 0x54fba1ffda268305L, 0xc880111a38792291L, 0xf2eb9417f1449b28L, 0x5238b7e0a70d7329L, 0xdca43f3c543f2e22L, 0x46c383c3194ad95L, 0x9b1496920dedc1cdL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xfce1374d8776fce4L, 0xd85cf3499c29e585L, 0x6381ae4ceac2c447L, 0x75d8bfce3f809fbaL, 0xc84d8601cfdad343L, 0x530e940cf4cb8ea2L, 0xefb4ce538637adfbL, 0xfffa4a98509411feL, 0x4c920237acca415cL, 0xd2ccfb0da7b7b4cdL, 0xb1aeaf131f14ede5L, 0x3fccc8897a3f8b4dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 17;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa6ba63c7c8b5c0b0L, 0xb3ea310874000a2eL, 0x195ffeb1984cbad7L, 0x4ec7cf559ee298e6L, 0x4d0ff374432cf77aL, 0x6d81b1299bb5dac6L, 0x46c19178a8adbb4cL, 0x6daa6bcbfd2d9deL, 0x14640fffeb9befL, 0xffffffffffffffffL, 0xffeb9bf000000000L, 0x146410L};
uint64_t A[8] = {0xfe9ef0ba0cc4d4L, 0xf2ce50c53403e761L, 0x3840a9e7a9b65f5dL, 0x929ccb9306859ad6L, 0xd7c9ea848c225f0cL, 0xc2c3e0c892683433L, 0x17b15172c1bc94f1L, 0x2eb749110972e929L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa11f421a0aa2fa24L, 0x8794ad527f1bd633L, 0x30974127d9b6769cL, 0x2128f6be0b3fdcdcL, 0x27ff13a84ac74c13L, 0xd54e9b4ffe5eefdeL, 0xd82701574b8e5ed0L, 0x793c8b3bfd67d38fL, 0x77ef7afdc21d01a2L, 0x51a0014c2ab6950dL, 0xa9277150a4fdf6e1L, 0x965e3920b3916e01L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 18;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x763a43482fc568dL, 0x95c376329182cb26L, 0x39c4800f0518eedL, 0xb8d3d9319ff91fe5L, 0x90876a0140959b70L, 0x92bf7c8f91230de0L, 0xac98b930824e8197L, 0x707c04d5383e76baL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xb7b80a3b92f33f24L, 0xebb8c6eda66109f4L, 0x3d4e414d5ae125d0L, 0xfe4bac5d667b36a5L, 0xf91df8af155ce79cL, 0x36c0fc867a2482aaL, 0xc67961734171152fL, 0x7ed40f8766c8520dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcaa0e562f417b8eeL, 0xc8b7887d12a2b468L, 0x160ad5e9a131d920L, 0x783a45d33176bc5L, 0x994f62e42b883739L, 0x9310a4823b3fa6aeL, 0xf4108f586b21b7c3L, 0xeb1c603ec15bb203L, 0xb05466070ff6e897L, 0x55f550bb14de3eceL, 0x39b1f94c6a8f96e3L, 0x4577d32bc68216c0L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 19;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8ac01d2acd15f5b6L, 0x284aaa1660485c4fL, 0xaf2809b89f07febeL, 0x963d038b93adff33L, 0x1d7ea29846ad73d6L, 0xf080df11d11982e4L, 0x70e8904ccda0cec5L, 0xfa3baabec14c73e0L, 0x29e2e3ffd33014f0L, 0xfffffffffd12f8f0L, 0xd33014f100000000L, 0x2ed070f2ccfeb0fL};
uint64_t A[8] = {0x793b80a73e500e39L, 0x3dc70d8c41726d51L, 0x327ba268cf29cc43L, 0x41754325b5ecc5aaL, 0xb9669b32568b37c8L, 0xbd6c661371ea683L, 0x73b527cb90a6ae1aL, 0xaa899fce49edefb5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7f984b83b2c9a9f3L, 0xa68a503a9b752f47L, 0xa9b89d3f716df94fL, 0x8daad25b4c5f605dL, 0x98e536a1a18ceeb6L, 0xe92e1fae5f09ea4aL, 0x213ddb826bc6ff9cL, 0x9fa3874b7e8ac4feL, 0x41670011231e56c0L, 0x3c180b5dc84e89eaL, 0x5ad7b3455f616c50L, 0x2b355f517a31196cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 20;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x3e017597744242b7L, 0x26e7308c19bb3268L, 0x8e69dd9e8e9f446fL, 0x663d1527fa549689L, 0xb21f0cda6a435f8L, 0xd5bf83bdf2c37f00L, 0x841e3c16d60d8921L, 0x54b6097b4bcf70e1L, 0xe6a8ffff1956L, 0xffffffffffffffffL, 0xffff195700000000L, 0xe6a9L};
uint64_t A[8] = {0xadfeeb8858cee75fL, 0xb39892a238929f1eL, 0xd5a7b62826fe4135L, 0xf19b7e5353944d6aL, 0x7d6929a823d46fd1L, 0x821afc9c9cdfd923L, 0xb00c038dd1f7bbf8L, 0xa1625858237504b2L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x72814dea2bb607acL, 0xb0e81e723a65ff52L, 0x46e7151c0bf71dbcL, 0x15a5773721921cb0L, 0xfadbca099dbdd660L, 0xad694562767ed43fL, 0x5d97ca7bcefbe633L, 0x3932bae601ee06d8L, 0x4aa3b9f27d9ca893L, 0xa64f55f03d64a5f3L, 0xeb4fa175970a2cf7L, 0xd0def64565dca3aaL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 21;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc8403902470343adL, 0x1a1baaa76d8805bdL, 0xa7496529bbd803a0L, 0x6b34413077adc612L, 0x85efc7e941325cc2L, 0xa875f5ce529d75e3L, 0xb26d7fbb7d8c5b7L, 0x39f59f66175adff1L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x984311822f72e228L, 0xcf7c32827d149166L, 0x6fa00b1fcb129716L, 0xc2ffababa18a27f7L, 0xeb8fb0bc65349b8cL, 0x96f12346df378f7eL, 0xe83b3b66e6a90e1aL, 0x3a5399fd2aa0179cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x160b9710b213ae4bL, 0x5e2a7648137804f5L, 0x4bd966885f0cffbbL, 0x34fe61dc187decc4L, 0xc889e441306aee87L, 0x1de7675a17d5b89L, 0x2c57082cc7fa90c5L, 0x866154366e7507ffL, 0xd002d87ee86f9e7cL, 0xb56087db0f8c8ba8L, 0xc856a5f70f3a9376L, 0x57cb6a7b29dc61e4L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 22;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2b46f080179b599fL, 0xd1cd2004ccc9769aL, 0xfe23852dad97e8cdL, 0xd773f16ec7400285L, 0xaadda1e58f084cabL, 0xaf3b27893af7d6c0L, 0xa3eb1163f9e7a029L, 0xe546d4e573bc27bbL, 0xf9ffffff05ffL, 0xffffffffffffffffL, 0xffff060000000000L, 0xfa00L};
uint64_t A[8] = {0x1ac9b3b95c98837aL, 0x8d80cea9a6380e97L, 0x68b05abd2b4c70a9L, 0x1297113175774cf6L, 0xf9b38f9d5ef51755L, 0x5566e3f4088317ddL, 0x279b1cdeee4dfc85L, 0x58aecf8f412543b5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6ff45bccb4012894L, 0xc200b9977e86f17dL, 0xd75d67c7dde9d70dL, 0x34f41dda1345aef8L, 0x7efa0919cda678aL, 0xc939c760d3f1254cL, 0xe27f942035ecbabbL, 0xe191806e0747f9d9L, 0xe9296da499fa4185L, 0xc7b2eee7a099e45eL, 0x4cd1b6b448aec129L, 0x82fe6d36a91e0353L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 23;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2f83a889ca881f6cL, 0x10b429a2811a47ebL, 0x2cd0bab9941a27e9L, 0xb7f1695a43020eecL, 0x4cb3c135b6f36034L, 0xdf4741a71b99ec5fL, 0x67f9ba802e45cbb1L, 0x2563c590f683e890L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x75b1deedf1dd81cdL, 0xcdedb3ab8dbc1d6aL, 0x6dbc4191c033ef74L, 0x99e398a2a8ab239eL, 0xd3e74166fb4fadeeL, 0x2bc2d83bc7d27b02L, 0xae7a6c8895365a36L, 0x163852f12b5f7327L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x715e9430ca63dc41L, 0x9ae4d4f5f7c4a00L, 0x85502913179aafecL, 0x9437c3fc5b796d1cL, 0xc9578dcf8460aa56L, 0x243a13b67e118d00L, 0x644288a98c1650cL, 0x95cbbc26e2c30ba9L, 0x462e366427556261L, 0xbd398a090ca1d57fL, 0x40eb86d82c19c78aL, 0xe1f22f4865a914b2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 24;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd1eeb7e05bfb4d22L, 0x8099d95dd283ba59L, 0x16868e2d862bdc8aL, 0x979129d2337a31e2L, 0x104e224dee0d0328L, 0x1c53f8aa95e66a2dL, 0x4ec17a11fcbae82eL, 0xf1c417884005d5eeL, 0xfffffffefL, 0xffffffffffffffffL, 0xfffffff000000000L, 0x10L};
uint64_t A[8] = {0x93dd30692eb231d1L, 0xa39f471f32cfa731L, 0x62f7ee7e271be610L, 0x24f77778117311eeL, 0xd42c2714ffcea877L, 0xcd80cbe14660ab67L, 0x47bd736b9e83ef82L, 0x76e3740442e49996L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7e56b3bca64974e8L, 0x38c6ab5b335903abL, 0x18647aa9661a4dL, 0xa46f152766af8da4L, 0x7b5492fb46ea1838L, 0xa7ce291d5bf76726L, 0xade0c6674b3b48adL, 0xcf296fc89c56a314L, 0xb41b1e1563683ee1L, 0xead45d4fd237709eL, 0x167ef6695ba339a5L, 0xfe64e3f3f97bcb10L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 25;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x33ec6868f044b10cL, 0xac09c4ae65578ab9L, 0x85ceae7c4b68f103L, 0x871514560f664534L, 0xb16c4303c32f63c4L, 0xf909604f763f1574L, 0x5509d1285847d5efL, 0x6ac4832b3a8ec1f1L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xb5cffedf0790a013L, 0xf1ba0f6e25458e39L, 0x66d546ad56e03b9bL, 0x7ce0061255f79ecfL, 0x7c2da8ba0847c739L, 0xc641e310a7eb8838L, 0xf3cc871d693e2a73L, 0x16439c6cd3b5b4e4L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1774f54b333b21a5L, 0x1accd45b972de084L, 0x942df1fadb5d0e50L, 0x4a7fba1ae4ee9783L, 0xfe76ff744045784cL, 0x79189c0565c270eaL, 0xc6cc512bc8ce913cL, 0xc5322a9365f47b75L, 0x81e39676174bef07L, 0x45b04abfbfee037fL, 0xe10698310b774a97L, 0xf5caf1bc4691599bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 26;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x32aa2b76cc10d472L, 0x8a5e9c88a35d935dL, 0x1edbedf72772fb74L, 0x6fd4184e96fac200L, 0x594773459b8f8e03L, 0xec4eb2d82685a5cdL, 0x1bbafb5dcde461b4L, 0x5b22fd1e7c375cL, 0x4ce2ffffb31cL, 0xffffffffffffffffL, 0xffffb31d00000000L, 0x4ce3L};
uint64_t A[8] = {0xff25a17d7870dc43L, 0x2882a3ad091ad8f4L, 0x86422227a32da1f4L, 0x5a90d00864bcd653L, 0x4879cd108c355101L, 0x8ded40b9d62f9fa3L, 0x2ecaba53bc0387efL, 0xafc51e23e464bb1cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x56835da08b1640beL, 0x4515ba75f578f377L, 0x497b81fb8eb33dc5L, 0xe94e556823567e5bL, 0x16497afbd0c6d312L, 0x7ce042647cf5029dL, 0xbc94928d40a35e04L, 0x10a042fb5907d1b0L, 0xf73c27ba1cf59be3L, 0x27240f7bb34305bL, 0xbfa840c496a15375L, 0xffdd50769821a4f2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 27;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x1851f9c63d860b69L, 0xdac11f445f82afb0L, 0x8687be821141749L, 0xa5e47c192244e059L, 0x64e16628fff2cfb2L, 0xad2d52d022fc29c1L, 0x12b3771785d7d300L, 0x56e333b03046dfc2L, 0x73db7fff8c247L, 0xffffffffffffffffL, 0xfff8c24800000000L, 0x73db8L};
uint64_t A[8] = {0xb7b80a3b92f33f24L, 0xebb8c6eda66109f4L, 0x3d4e414d5ae125d0L, 0xfe4bac5d667b36a5L, 0xf91df8af155ce79cL, 0x36c0fc867a2482aaL, 0xc67961734171152fL, 0x7ed40f8766c8520dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x878adaba9cd82f0dL, 0x66916fbb007e754dL, 0x81d388eee1d83613L, 0xba4d4745411d00fL, 0x8005824b86c8872dL, 0xadc6268814926434L, 0xc0cddc632b66d2eeL, 0xed9cac1cd009787L, 0xb9b9ef48ff68f53dL, 0x98db9601a2556d10L, 0x8e46c059f0128ef0L, 0x8e8b0308022ed1b1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 28;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd0288cb552b6fc3cL, 0xc5f4d6cd3ac77acdL, 0xa3a14e49b44f65a1L, 0xb4241cb13298b343L, 0x460d45ce51601f72L, 0xd667da379b3aa441L, 0xb675511e06bf9b4aL, 0xd5cc8c2f1c040abcL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x47b8c90e0ec452b0L, 0x8691f46ed9af1fa9L, 0xda120f3433f2d27eL, 0x160837d249afa40L, 0xe0053424c4c03fc6L, 0xabd0d5874b2e52adL, 0xe28134da897595edL, 0xc9d2fe827d859fdcL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xac65c67cd65b03afL, 0xad63902955ce74efL, 0x3c40205247c6d58cL, 0x875931b4813d6d5fL, 0xf769614f0acc326aL, 0x531404c0d162fd7eL, 0x3c7f555e8e8f132fL, 0x7876431970cb11d7L, 0x77903c57bc0d5674L, 0xc09d1da19ee7a4dcL, 0x3670c0eb7fa36cdcL, 0x4d3c66cbf20246fcL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 29;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x1564370496fb8b1L, 0xc4b3691f14fa6e0cL, 0xce8fe0f30ecb3239L, 0xd785477a15edd4a6L, 0xee2eea470798bea6L, 0xa9d537cc1e80bc1cL, 0x6a1dbe7233846472L, 0x8ecf75faf1a21ba8L, 0x546d980fab9267eL, 0xffffffffffffffffL, 0xfab9267f00000000L, 0x546d981L};
uint64_t A[8] = {0x81d4d67d5303aa9L, 0x55d6984e2ed8d949L, 0x9ea7ce6365f0934aL, 0x69b60cd9343b297aL, 0xa916a98dc09558fbL, 0x4a43bfd951bdba86L, 0x6c7cc30329ddb815L, 0xd6b16ee90d413600L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x81c4208de4a64582L, 0xfc280ac0dc29ce50L, 0x6d9744160c08c202L, 0x44d22daebc4873f7L, 0xbee686ab0c451cb0L, 0xef76b9d65f138311L, 0x4ea61f4fad951565L, 0xd0e16cbf64627fa6L, 0xc6ebd634da4f0df5L, 0xaddd26bb00e50898L, 0x28d0541518e1c6e8L, 0x517092d57caeff89L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 30;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x88a42ab51e710a07L, 0xea7008b5135a0378L, 0x79a0f3814d753391L, 0x555b95c4dcf2f0faL, 0xaf0c62c3d6b32facL, 0x60beb7b35c46def5L, 0x1a0e4e52fac0f79aL, 0xc86bdf45232f2a75L, 0x6bcc41e89433be15L, 0xfffffffffffffffeL, 0x9433be1600000000L, 0x16bcc41eaL};
uint64_t A[8] = {0x633882d09d70b2fL, 0x751a305fb9992f1dL, 0x7e062c54bcd8ace8L, 0x52ebbfcdf7150d28L, 0xc9a8d89c7d00571eL, 0x6688e25bf90134ecL, 0xb8c44a8ed98d1f32L, 0x404354ed7f4ab63fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xfe4e16af5c296e16L, 0x6af4ac5c42e49f03L, 0x6778bbf4f5ee25adL, 0x57c5c64b199b8083L, 0xd3840fbef698618dL, 0xd1799bc2593a62c7L, 0x201f70f594104ecfL, 0xd29ad64fa843651dL, 0x66b5221623ebc77cL, 0x2303af08094bdca6L, 0x1aeb09ccbf3b6cbfL, 0xd802308747486528L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 31;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4c2bab1b8add53b7L, 0xcb9727eaa2d17c36L, 0x2100d5d3a8d063d1L, 0x69d44ed65c46aa8eL, 0xa062499846fb7a8bL, 0x6651f7017ce477f8L, 0x778afcd3a837ebeaL, 0xa084e90c15426704L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x29c60f9061b2c396L, 0x8876c61e6c81ab4aL, 0xc7ec0daf4d390d9bL, 0xc8a74fa90760ad64L, 0x23e94a05535cebf3L, 0x18eff73a7322ab63L, 0xc340e0c9b0b00d4bL, 0xca5220c37408de5bL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x45d67dfec119f83aL, 0xfdef04d65e504726L, 0xebeae47929c3639cL, 0x681b6ea26cc36c0dL, 0x8a28ea05d4ce4ea4L, 0xbb84f823c77799cL, 0x9ace5d5e0ca0be34L, 0x4711001015537a38L, 0xdd9a6473d6d56fdfL, 0xbcdf9e33c9b02f14L, 0xa6eb37dca468a9caL, 0x5ed300d2ab1a02d5L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 32;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd8d833b0863f2fc1L, 0xc4a77133c9152440L, 0xc711ea7c62fc87f0L, 0xf5bdd9372f5626f4L, 0x7c483dd4bd08dd5bL, 0x45787f29d43eb3c5L, 0xcbfcc8f14f83f3adL, 0xd905124b5330f08fL, 0x12167fffede97L, 0xffffffffffffffffL, 0xfffede9800000000L, 0x12168L};
uint64_t A[8] = {0x254a4a3e09ba48fdL, 0xf5f9a498bf1bfdeaL, 0x7c18faa630900f7eL, 0x113542810b0284cdL, 0xe97fbab46827f334L, 0x5b7d6c595db8b18eL, 0x669025d6306e5844L, 0xee79ebb98c19a4cbL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7f46d63eb388b8a6L, 0x75de54f97f06293bL, 0x4003e128d8baccf2L, 0x35b49df810b2349fL, 0xe04e711e4ab12797L, 0x7c9f675d686e6b94L, 0xf27dcd43f4fdcdc7L, 0xfa95af06ee330853L, 0x363031e12e83be97L, 0x13aea2b5fc43341L, 0xcc95926c2d56899aL, 0x6d143f2bf6845750L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 33;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf2ce78da527b0e23L, 0xef4971c55d204279L, 0x2138ca7dc35846f5L, 0x10d3f742d32f4260L, 0xa196238134f62855L, 0x8023537a7dec4dc0L, 0xd26539b4d7066b9fL, 0xf6021f19f18408c0L, 0xea42b722155ca0aaL, 0xffffffffff9f57cdL, 0x155ca0ab00000000L, 0x60a832eaa35f55L};
uint64_t A[8] = {0x2d0f1be2b5577cf9L, 0x8decdf26c01ce141L, 0x7e28a0d562d7881L, 0x8218884b2f38e1d6L, 0x707320391e7826faL, 0x36925b3cb704a1fcL, 0xe77da7d78929b20aL, 0x747c0826cd4f4e7bL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6a9dfbecd7679955L, 0x892ef45bc53427cL, 0xe54f7f6918ae0f4aL, 0xd4ef4f868ecf07aaL, 0x6ad89678cf67facdL, 0x9bd59666e46695bcL, 0x99d9eba3029b8d6L, 0x9df444a2e1e7d989L, 0x2354365e92ee3dc3L, 0x9928aa37c1ad26fdL, 0xeb0c64b1c167314bL, 0x7fec8d2ab65e2af6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 34;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xbbbe776c3b06382dL, 0x28dce0124cf06d93L, 0xf3e8a5a8d939d98cL, 0x39c5f53d7fd00690L, 0xab623d2c4121e279L, 0x590dc5a09768f923L, 0xebf4b2c8188d809fL, 0x8c61f46f48712a12L, 0xfffffffeffe65f00L, 0xffffffffffe65effL, 0xffe65f0100000000L, 0x19a1000019a0ffL};
uint64_t A[8] = {0x863adcbfc3e11936L, 0x132997833c5875bdL, 0xc66fb8e48cec6857L, 0xb9ec70c15113985fL, 0x2dbe3b667dc96eebL, 0xcdc946093e60978eL, 0x17495e3dd74c9d3bL, 0x2babf31ff018f49cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4438fa949763708eL, 0x2ef6f6284035fdaeL, 0x2c7bc67e940f5dc8L, 0x372082bc46b0246fL, 0xcf1e152e93a26076L, 0x16ecdcf6cb6c254aL, 0x4b5806cc21bf1d43L, 0x5a611e223e99f8a3L, 0x77ace7f33b240738L, 0x145e9ef8eaba03e9L, 0x80634d76b1cbc3abL, 0x2be3dfbddb108ed8L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 35;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc5d2767e2f1a0d67L, 0x50ea317973864c12L, 0x67d4c564f28528e1L, 0x8e7d5929caba6cfeL, 0xea7cbd62170c82ccL, 0x2f0b54596f0391afL, 0x48bd4d0808160d96L, 0x7393682056092b24L, 0xb3773e3f4c88c1bfL, 0xffffffffffffffffL, 0x4c88c1c000000000L, 0xb3773e40L};
uint64_t A[8] = {0x3ef7fe59ea3221baL, 0x32b0a08a947eb0fcL, 0x14e3248935cb57a7L, 0x4b58c0845c0e281bL, 0x2bba72ad6d2715cL, 0xc55188170fd69b7eL, 0xf77dd00bfc38ed37L, 0x6f3fc230de80a5dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7dff2653e5d31b10L, 0xebeef3cf7f87dd15L, 0x4a6bd5f6266c9c2aL, 0xf8b874398ea5f92bL, 0xbe1c10e99a60a575L, 0x8124ccb69b04acfdL, 0xdc78eb3bdb62fa26L, 0xe8f47ddc0c01a383L, 0x2ac829cb9613838eL, 0x4c0d7a96b3753819L, 0xd4e6bd1e872f512L, 0xc2b9585c68bb47fbL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 36;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6a4c013557f2b9e8L, 0xf72e079fd1e5763dL, 0x36df500915a3d018L, 0x500770c9c328cf24L, 0xb2c21e701db5a4bcL, 0xbbd561477effb9eL, 0xad289477433405b1L, 0x8f4096686d6d9f50L, 0xcf94d1ff2e17ace8L, 0xfffffffffdac7ee8L, 0x2e17ace900000000L, 0x2538117d1e85317L};
uint64_t A[8] = {0x13b094a94e0de8bfL, 0xc1192e9bebd3fd5fL, 0x4426583cc2bc2fcL, 0xe3874e85b10c271L, 0x721a3a6c6b0185acL, 0x5bbf5051314aa975L, 0x8a3c17181c4402cdL, 0xe4a2b66f3663fbf4L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1b02413f3d3ebca0L, 0xbbd224922ba191ebL, 0xa23fd98c6ee1e3faL, 0xbd1a3f345c8fd566L, 0x8613026d5bf087afL, 0xf42372d442d89f03L, 0xee63ffa49472e050L, 0xdd3c7bd3591c6345L, 0x410457258d281af9L, 0xde59603f30e52fc8L, 0x4db6d14ad884d070L, 0xb577a957aa88be9cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 37;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf321e9de744c6ad2L, 0xcdc70e15993aea70L, 0xb95cf0be74dcc589L, 0x3a167d90f86d6c54L, 0x7fa24414cc3cd05dL, 0xe16e43069c53e755L, 0x76933e2a56e412fdL, 0xfd8d6325991762bL, 0x1cb90fffe346eL, 0xffffffffffffffffL, 0xfffe346f00000000L, 0x1cb91L};
uint64_t A[8] = {0xc9a5bd13954b9ca2L, 0x566feeb4d61328caL, 0xcfd7bf48e54e1acdL, 0xeb2603b57b7acd4dL, 0x7bcdd0ff094f23f1L, 0xcb8721ecb3ec12b9L, 0x9e4cbd67c300f661L, 0x31ccefd32ba4dc4cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xdb7dd1c94a9fa9abL, 0x40048094f8dce548L, 0x586487db97c84212L, 0x41896e42a9b9cc10L, 0x6d3683e8a5232f6dL, 0xbce37aea53541eb6L, 0x6f3727fd3e9145c3L, 0x202a08bc3ed3e299L, 0xe4f296348ca52d1fL, 0x1b428adb7ebf5e61L, 0x23f6eed6532fdc36L, 0xe999b6e0ffd6e7c6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 38;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xdf3ce991d2d510f6L, 0x9f81149c449b37eaL, 0xd999ae644d590c3bL, 0xf82ccc8afdcb64a0L, 0xb9e5b2f376fa3f1fL, 0x118e3382260e7b98L, 0x9eaaeb3e89c4c4fL, 0x48eefcc582e18af0L, 0xb65313603f200a80L, 0xfffffffff5731de1L, 0x3f200a8100000000L, 0xa8ce21ec0dff57fL};
uint64_t A[8] = {0x82de615608c76a8bL, 0x9e0760f5e009de70L, 0x13dcc92f9c572952L, 0xce00bd446f820d48L, 0x47ec470393401b88L, 0x477a8089293b49a2L, 0x5c437d80ee42e88dL, 0x3e4356a607a49fe2L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7bf75c8a1f471b57L, 0x22ce8c9c485b8006L, 0xa87ed40355af06eaL, 0xab609499c7a0225dL, 0x182426871d21c912L, 0xcd9381c97d046696L, 0x675159a6735a5923L, 0x953e6532c5927b40L, 0xf73dfb8e1874c6aeL, 0xceb45a17a4e2a0fbL, 0x55ff54c3cb9ce6dfL, 0x78a0666faf351a3dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 39;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4b45458226c622e7L, 0xc60356d7da17591dL, 0x4381f85b7c03a21cL, 0x26c807842e2d8caL, 0x3c7e5e74ac572ec1L, 0xde18792fc19f2c8cL, 0x263568e0525f04dcL, 0xa2b0b26233640218L, 0x78361a4687c9e456L, 0xfffffffffffffe9dL, 0x87c9e45700000000L, 0x16278361ba9L};
uint64_t A[8] = {0xd649102ec1fb2df1L, 0x9c149775e9226d96L, 0xa3b71044b21decdaL, 0x9d0dfc8ea449fc3bL, 0x3314dda07d498cf2L, 0xbe36114a7ea752a4L, 0x3108cad73819c477L, 0x55f13bc006e22745L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xf20f746cafe636L, 0xd53bca518c2cf084L, 0x38d78c9be0ba537L, 0x2285a26e818cbedeL, 0xd610096404633f9aL, 0x42c434dc37e5163L, 0x172bfeff8e77c6bdL, 0x3730b2e56d626405L, 0x50de97f3a70ce36bL, 0x1427d9d3892d9014L, 0xb9549a4a86de1726L, 0x7c6db6a28787f9b9L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 40;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x47d014641733bd6dL, 0xfef8db8a4124dbd5L, 0x30db142dbdd868eaL, 0xd47c5fe4eb0040b0L, 0xabfb2cdaa2d772d2L, 0xa6ea6b08185c17a2L, 0xc8633460403da23aL, 0xb278eff690dc24c7L, 0x843fffff7bbL, 0xffffffffffffffffL, 0xfffff7bc00000000L, 0x844L};
uint64_t A[8] = {0x76b85af13143ff6L, 0x25e08eed9e9aa27fL, 0x3e3d0488ffc51120L, 0xf8c81b242528c884L, 0x418e685027128311L, 0x63ac37d528a681efL, 0xf0a07a9732ef1690L, 0xc7fe6aa567d1367fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x65a1dd73367fbe24L, 0x2c96ed0c520c7a01L, 0x47206ac110b6ee2eL, 0x97486ad8f8c1ad7L, 0x276102ade197c48cL, 0xa8f42a18af32bf3fL, 0x3aff0195feb9f120L, 0xccfe816f113db0d2L, 0x3873049b476cf46L, 0xbff713aaf5d20580L, 0xd64cdb1513209724L, 0x339d28ac65d8cb1bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 41;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x1531b3de8bf4a715L, 0x81615b8a473d4da1L, 0x341842c77d94f082L, 0xe102780ac82735c0L, 0xc92adbb5b1bcb5f3L, 0x12ee426867c11b47L, 0x5828f00840051c39L, 0xc9728a43135274b5L, 0x9502f8ff6afd06L, 0xffffffffffffffffL, 0xff6afd0700000000L, 0x9502f9L};
uint64_t A[8] = {0x5da30e809bf1f538L, 0xbe5d744b3a90ab99L, 0x9434dd7251db0f1bL, 0xed877b75c958ef7cL, 0xafe213dbf0592657L, 0x9805f40db8d4bce3L, 0x1253471881081adbL, 0xed43c8beb572b391L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x87fab480ee2b8161L, 0x3b44bf815a6dfbbfL, 0x9ad94dcdb0d17b47L, 0x6aaffaa31934d1abL, 0xee6685760cabf101L, 0x89b3abbc8d90c3f1L, 0x60175ed2c49d6c92L, 0x1b74eae668b2afabL, 0x8d00a045f8830827L, 0x4d5fd5a3ce88c457L, 0xd68a59d0e85d22f2L, 0x4aa998bd15ca0c67L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 42;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd176448e35b23e27L, 0xb00eea8a5d34f708L, 0x294b12e1ca1b04e0L, 0x46ce85a9e25a441eL, 0xa48558f2fa1bd2fL, 0x77c52d75519978d1L, 0xc45e52db3bfffc8L, 0x5ce885392bb80ef9L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xc7ddf7864ac64482L, 0x80cb53c4c9ac79e0L, 0xb47cc1f1216cd550L, 0x1df4d36fc0aec63fL, 0x7c792a6f445611f5L, 0x7002065a567a0793L, 0x817c6261de6732b9L, 0x753e20a3ae511746L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa63fefe087ee0a27L, 0xd3361199c0ee65e1L, 0x4b9d828ade141bbcL, 0x1155eca32998ca21L, 0xf441598aa6a3c35fL, 0xbe90166645ad6140L, 0x16f7c49207b6063eL, 0x2b7878090ca2af64L, 0xf667b2f71514065bL, 0xd0bc693a6c7782d8L, 0x8b31af105751d06fL, 0xd7264dc5de548220L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 43;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x9624fa491af2b23bL, 0x99d481d9aa936f24L, 0x965d676f0592440fL, 0x7820850c249ed06eL, 0x2f7a9f7492363053L, 0x1e723b82b1d2a6ddL, 0xc6eed0222517903dL, 0x52d9c33dbd0e8d00L, 0x2e140620d1ebd03eL, 0xffffffffffffd65fL, 0xd1ebd03f00000000L, 0x29a02e142fc1L};
uint64_t A[8] = {0x1194785fc0ebd864L, 0xae08dba305d1c30L, 0x637a496883bf13e0L, 0x1e59d7ad07931b9L, 0xfe138e7c3a8da79fL, 0xfaa2ea66baccab45L, 0x46610f593244345L, 0x990198536bb2cc87L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xf26e0ecd5b43de4eL, 0xbad6d6ee2c30a2e1L, 0x4b1f0620b53e53d9L, 0x2931960927d55b6aL, 0x5e19fcda84a45e69L, 0x635401ef8da173b2L, 0xc033ffcb1a0b373cL, 0x32ffcc894676bdb4L, 0x16ccd8cbc016b06L, 0xa1b53988d828b745L, 0xc8165207a527b6a3L, 0xcd40e02703321785L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 44;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x33ec6868f044b10cL, 0xac09c4ae65578ab9L, 0x85ceae7c4b68f103L, 0x871514560f664534L, 0xb16c4303c32f63c4L, 0xf909604f763f1574L, 0x5509d1285847d5efL, 0x6ac4832b3a8ec1f1L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x57fcaf64b5e8d6dbL, 0xf670e79ac97efbdcL, 0xe12253fbdb991b94L, 0xa928a6d84768c868L, 0x1d94d6153c3e2656L, 0x2085b6e8694a3819L, 0xea05005e197a2805L, 0x8004d784b244753L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x5790c3752a4a7baeL, 0x2b96388e098c10adL, 0x64f6b2ac15904253L, 0xe1f65d6c74f1f399L, 0x7a8b28f324f9b67eL, 0xe56ad41e02407d1aL, 0xac40e71d23df4203L, 0xcae16dd6fb239e51L, 0x241046fbc5a425cfL, 0x4a6722ec64277123L, 0x5b53a57f90302a91L, 0x2213928238028334L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 45;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x70805e57317e0201L, 0x907e89b301e24452L, 0xac131ca63101ca91L, 0x8c9859401adc7ecaL, 0xd7ef5f2ce1cc3f05L, 0x1e7aabd16a637fe6L, 0xf31f607c3b46b523L, 0x739e14e2da1bf421L, 0x1b0828ffe4f7d6L, 0xffffffffffffffffL, 0xffe4f7d700000000L, 0x1b0829L};
uint64_t A[8] = {0x40bb8a1ca9a92a51L, 0x112746e2f16e4f64L, 0x779bb091f4b4168bL, 0xb2ba97669274864aL, 0x37f260b9e557fe9bL, 0xf53a2212b22d0d90L, 0xe2f8e1c67da8af3aL, 0x592870011c59d7adL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x99b42ff1e482252fL, 0x6dbd27d39c4815caL, 0xc432845277dfa86L, 0x25b6f6408de90210L, 0x5d7e1cf8fea01d30L, 0x3de171c7b3c52ff8L, 0x691b1652e01b8508L, 0x8038fc64c35cada3L, 0x1dec5b6c362a91ddL, 0x76c813364af845fL, 0xd65ed20c1ff7bf6L, 0xacaf01f57dfe48b8L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 46;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x3362bae22c3ad946L, 0x862508037908c968L, 0xedffad89c6f6e3edL, 0x46870c7f6e823724L, 0xd19a1be06ce75207L, 0x3c898ab747b7c7ecL, 0xaeac44c7816a97fcL, 0xb3b1addf02c166e8L, 0x9f67287f6098888bL, 0xffffffffffffb10bL, 0x6098888c00000000L, 0x4ef49f677774L};
uint64_t A[8] = {0x81d4d67d5303aa9L, 0x55d6984e2ed8d949L, 0x9ea7ce6365f0934aL, 0x69b60cd9343b297aL, 0xa916a98dc09558fbL, 0x4a43bfd951bdba86L, 0x6c7cc30329ddb815L, 0xd6b16ee90d413600L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x2933915b57d78019L, 0x6c24718cfdb1a060L, 0xebf0e67183638e04L, 0x500417ee91600b9dL, 0x30a61f8b30980d31L, 0x5f7ffb6b3f4c4f90L, 0x121a0af670ab6281L, 0x8945c8cd814e6230L, 0x8724ab50dce156c5L, 0x72c0ba46829e8818L, 0x9947d6bdeade8767L, 0xd2bb4576a82b74a8L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 47;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x948fb3f76932e631L, 0x1707165bb939f40fL, 0xabeee3e9369a6067L, 0x7d81fd488418cae4L, 0xd8d37d942785971dL, 0xed5cf82dc911847cL, 0xbdf176108c7f9dbaL, 0x5a1dffeabd468eL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xff25a17d7870dc43L, 0x2882a3ad091ad8f4L, 0x86422227a32da1f4L, 0x5a90d00864bcd653L, 0x4879cd108c355101L, 0x8ded40b9d62f9fa3L, 0x2ecaba53bc0387efL, 0xafc51e23e464bb1cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1077f11af012b429L, 0x4282157fac4605a7L, 0xe10e8659763cebcbL, 0x314e86ee5c9955aaL, 0xd2ed5e7017b73140L, 0xe069f6cff4862b0fL, 0x9b49a41191d4e15eL, 0x3ac00950c7d4ac5eL, 0x6a95ed860f3df612L, 0x117b8d514fe0e4e4L, 0xda533e3e6c93418cL, 0xdd0ed2bfe0a40b6fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 48;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xfdc777e8e93358a4L, 0x6a0b0685d2f8ba3dL, 0xc99ffa23e3912a9aL, 0xfc611352f6f3076L, 0x793e8d075d5cd074L, 0x9de917da153a35b5L, 0x640c2d6a4d23fea4L, 0x94a787bb35415f04L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x76b85af13143ff6L, 0x25e08eed9e9aa27fL, 0x3e3d0488ffc51120L, 0xf8c81b242528c884L, 0x418e685027128311L, 0x63ac37d528a681efL, 0xf0a07a9732ef1690L, 0xc7fe6aa567d1367fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6deb44bc9756dab7L, 0xf63b6eedec5ea412L, 0x40d5e3888d4e093dL, 0x3e189b0ec11377d5L, 0x994219d97b16f98aL, 0xa167ef8a7bc9184aL, 0x352205301b7ed7dfL, 0xd6802c8dcdaee3c1L, 0x9a40dc529e0e752L, 0xbbd58867cba1e841L, 0x749d0a661c33e686L, 0xe90209eef5b9980dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 49;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6dc659d335973a5L, 0x7a96346bae414cecL, 0xf4676ff40613baffL, 0x5eb3509214e6a363L, 0xd346790b3ed19f35L, 0xca69e394c894ac76L, 0xdf5b845a87a92f6eL, 0x592829ffc8e32ebfL, 0x289e6fffd7618L, 0xffffffffffffffffL, 0xfffd761900000000L, 0x289e7L};
uint64_t A[8] = {0xfd10d4229c2a4473L, 0xd255f5c688011591L, 0x6168ae5f30b59dfaL, 0x6f939d68a2be35f5L, 0xc9594125c2f30c3dL, 0xfaa6fa91bc6665c6L, 0xc1cbfb07ec4e60e8L, 0x5f41d10cb649b4c6L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8f1932e2a0b5d9d8L, 0xa3738afbe9360988L, 0x883b7698fc42697bL, 0x57ddf1274b0ae3L, 0x89c234cb7dedd5f6L, 0xf5e1641b37aabe99L, 0x4a08eb0239bcb423L, 0x72a7fe7d3c0437ffL, 0xf2a3c2a7a4f43e79L, 0xf0fe4a2982f1bfccL, 0x985f3e02648d5550L, 0xca0e08859ba3923cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 50;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x53fa43894f4c22bcL, 0xee5614c514b56902L, 0x958f7a6dcf89b2bcL, 0x9dcda93232c41ad4L, 0x9d9b7b0ac7aa6bd3L, 0xc8975e8fddbdf24aL, 0xf1f379a9c74ceb83L, 0xc3f7afcee0c6c49dL, 0x14bb6d14eb38d9ccL, 0xfffffffffff446e1L, 0xeb38d9cd00000000L, 0xbb91e14c72633L};
uint64_t A[8] = {0x6dd9dd6684ee22bfL, 0x41b1dcb877b6d686L, 0xa11ded59ce7db4f7L, 0x520d5b964031efacL, 0x71fa5242e827ced5L, 0x3f2ef814d940c167L, 0x227a98c6572d686fL, 0xb64b316dec22c9b9L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe654b38838c22e8bL, 0xbbeaa54c124732ceL, 0xc88f3de7a13e956eL, 0x75204b6e3974bd10L, 0x28daba66ab7d78f1L, 0x1ac0f9cf2955e900L, 0x10544bbdd82ea2b3L, 0xc86591285bf0d84dL, 0x9b09c1a38c1af2aaL, 0xa35571f84cb0469bL, 0xd3a3262e10e60d8cL, 0xf25fcf2579a9489fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 51;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x1691b704d2f245e7L, 0x2e39074538318100L, 0x762a0cbda9d200ecL, 0x6c180755d321a188L, 0x67025fcedc8c0ed5L, 0x4a8040176673f939L, 0xac80e003e07c81dcL, 0xe395a9a1ad36203cL, 0xe1780fff1e87eL, 0xffffffffffffffffL, 0xfff1e87f00000000L, 0xe1781L};
uint64_t A[8] = {0x46ed86f948a08edcL, 0x3f5b4c65383e91dfL, 0x8f4f9ba66ae7ead8L, 0xca5477de61ea9046L, 0xa091153d7642156fL, 0xc433ce04b59fca93L, 0x3b33c627d44fcef4L, 0x51c35033d6d90800L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x9996f0403dcd1c4fL, 0xaacafd957a145537L, 0x5765ee332f8002c2L, 0x5bec8fc75867c2f8L, 0xa18ab2f3f3cc7a61L, 0xd04b6eb6bd39265eL, 0x101e7a7bdb901c85L, 0x6bf50c16690a56ebL, 0xc9e48a112f45075dL, 0x178a6b0fa3bbbafcL, 0x5498c169a9709f44L, 0xd232f97293c34e76L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 52;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x41e854ddb97df4bbL, 0x16e4967223ca5b45L, 0xa0ff234fb175e868L, 0x6a8af6703f627dL, 0x7cbefa4d1c556bfL, 0xf54c91bca87d777bL, 0x67cc12c7c20e416dL, 0x76805ad688d899a8L, 0x1298ffffed66L, 0xffffffffffffffffL, 0xffffed6700000000L, 0x1299L};
uint64_t A[8] = {0x5407a49b4faa0cf2L, 0x7eb23d3000f5ecf8L, 0xa2db87227dff4d2L, 0x6f0021dca8ee51c3L, 0x3e855bd6d766cb88L, 0xf50f8d1d5397f0dfL, 0xd0b1f024322e5746L, 0x3f859e44807206L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1460e682a950ef31L, 0x83df5e92835506aeL, 0x2c147a1098ddf8adL, 0x80c7393196f57187L, 0x371ac9e4f39c35bcL, 0x84adf7e0599d55f8L, 0x2533effefedd3dacL, 0x6454378adf221c9L, 0xd479c23d2ef20d29L, 0x4a375803fc698932L, 0x297765d8e54ae308L, 0x1781aa9269fd2dbcL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 53;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x5dd52e3523850b27L, 0xd0022c90c9f5aca0L, 0x5966e490a231775fL, 0xbbb9a9924f7de93L, 0x19f0440ab3295f7fL, 0x3b1f1328174b1b0L, 0x6df61e54a439b863L, 0x49ceb09b07c8360L, 0x458d5dcfba70cfaL, 0xffffffffffffe2d7L, 0xfba70cfb00000000L, 0x1d280458f305L};
uint64_t A[8] = {0xf88efc2f992a1840L, 0xd1307b0ddc6b1805L, 0x7ceb3c4ce14ad2f8L, 0xdf7af4100a29b85dL, 0x40eb4ee6d7192864L, 0xf417e1adbb353aaeL, 0x2fa050056a2dd698L, 0xdd87442cd9c57692L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x5e00c8f2e5b4ac8dL, 0x4294d2c67f2ba27cL, 0x22f50b7604ef4896L, 0x2d0608361b083c7fL, 0x6344b8a73e3a64f5L, 0x5d3ce5787c06f636L, 0xd3299e8474edad76L, 0x6ef72bcc794fecfdL, 0xdd797db0a8f67f22L, 0xf406e6a85994df72L, 0x7d3439ce7e866ed6L, 0x13f09637e4e17140L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 54;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x7b0249f059d9dadcL, 0x8ed48bc47b01525dL, 0x67bfcdfc8933cf6dL, 0x9834d6ab6c5ab5a1L, 0x7c5eb50e55ff7be1L, 0xd76f5fbd6bd81e7dL, 0xa121040256f0749cL, 0x74be5935714b91a1L, 0xdcbfffff1077941L, 0xfffffffffed37941L, 0xf107794200000000L, 0x12c86be0ef886beL};
uint64_t A[8] = {0xd4132c949782a702L, 0xb9c7481ab24decfcL, 0x1c1aea428adc92aaL, 0x700b7340f3884e72L, 0x7400a35dd27a2b5aL, 0x65444adb78515317L, 0x9866c40489564d2eL, 0x599c5f75dc920771L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1399cec0819bb6e3L, 0x783a0d82c5ddfc0fL, 0x3848b98a0f52f7b3L, 0x2277f93fb562a6f0L, 0x92df3830e7c7bb5L, 0xb5c51f7a22ab2378L, 0x7f19631d26a8694fL, 0x7e9dcc883e2caacaL, 0x53ed7ac1fe125dL, 0x55d34a325242f8eeL, 0x34b038df9b9c59cbL, 0xd382767312b8a0ecL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 55;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4fdb79bcc6c31920L, 0xd7fbcb8234f62873L, 0xf102efde62974914L, 0x1517d18d2134496fL, 0x72c4cace2a3506d6L, 0xcb071b97bba71437L, 0x6e4667b9b3de018cL, 0xd551bd00d5074cfeL, 0x16a973ffe9568bffL, 0xffffffffffffffffL, 0xe9568c0000000000L, 0x16a97400L};
uint64_t A[8] = {0x5da30e809bf1f538L, 0xbe5d744b3a90ab99L, 0x9434dd7251db0f1bL, 0xed877b75c958ef7cL, 0xafe213dbf0592657L, 0x9805f40db8d4bce3L, 0x1253471881081adbL, 0xed43c8beb572b391L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3d32182527195236L, 0x3f1e745b52a63e56L, 0x10a00f3c1947a11cL, 0x24b2e138d5017dc8L, 0x7228bc9fceaaea42L, 0x70de5a7d799f68f6L, 0x1aa4dc26b1dce5a9L, 0xe1001e5deebda651L, 0x493b1884919da3cbL, 0xe30769f667c735edL, 0x8e69cd9df2aa3e3fL, 0xc48a6d3ef7b22f21L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 56;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xdd421b5d4a210364L, 0xf94aa89b40750d01L, 0x49c7cb94fc05804bL, 0xf19f382e92aa7864L, 0x574cc7b293786791L, 0x11f947e696cd0572L, 0x30a119fdd4af1ecL, 0x56cd001e39df3672L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x341b086b676a2fbeL, 0x68db382f19ca019dL, 0x697e8c0627dc6ddaL, 0xcdb9a82de60af300L, 0x278c89f1cfbaef62L, 0xc70d2f3278e0a3bfL, 0x26f4711925a9c4ebL, 0x846dd6f74b72b663L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xec2d42539c001a3cL, 0x9d661e02c83c9defL, 0xa6c0217fddda9b8eL, 0x8ad1552439b0425bL, 0x57f04337dbb338f4L, 0x251d11e3d495206bL, 0x6910e05e718234baL, 0xbd170b8e08fdf21dL, 0x56d8ed0d1d492c5aL, 0x6f908f93d954f49cL, 0x1fb6c0722bd6ed8eL, 0xdc1a6fff53607a9bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 57;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc368b339c6f95675L, 0x3dbd797b5c84fbb0L, 0x3418c27a0be93456L, 0x5b75ed393e57504eL, 0x679e3610d19c8e0fL, 0x4e6c4406814e1cc7L, 0xbfff7e5f5bfb6821L, 0x28fcd703f700ac0aL, 0xa0ffffff5effffe6L, 0xffffffffffffffe6L, 0x5effffe700000000L, 0x19a1000019L};
uint64_t A[8] = {0x3ef7fe59ea3221baL, 0x32b0a08a947eb0fcL, 0x14e3248935cb57a7L, 0x4b58c0845c0e281bL, 0x2bba72ad6d2715cL, 0xc55188170fd69b7eL, 0xf77dd00bfc38ed37L, 0x6f3fc230de80a5dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcfa856057aac93faL, 0x2161144405b50810L, 0x77743493ba0b3e12L, 0x52d3cbc1b2423be9L, 0x424877626481784L, 0x8ee463a8fac15154L, 0x7641fb38f07339b5L, 0xad2369591753402dL, 0x5e56eaadaf3d56ecL, 0xf836f23f378dfb0eL, 0x1b32120db132a467L, 0x7131195820db82b4L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 58;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x20a4eaf655becf25L, 0xd1e75d66949dfb36L, 0x6d37b12360725b2fL, 0xb30a7f3245cf99afL, 0x54b9736178d7f7c8L, 0x3174c7468984423dL, 0x1779987b53192463L, 0x9bc8abd920656359L, 0x960fffff69efL, 0xffffffffffffffffL, 0xffff69f000000000L, 0x9610L};
uint64_t A[8] = {0xf667eb6d85778c2dL, 0x69bd3b98be8a0269L, 0xd0d881388c8d4dddL, 0xbd27516f04873c53L, 0xee39a1f1e2a7175L, 0x9be12c7128ed3a77L, 0x93d4ff32308e256eL, 0x40f84dcd934224b1L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4066819674dc76f9L, 0x201ed84505e3fcf6L, 0xa9cb277c045fbabbL, 0x33dae1b6f0831d4bL, 0xaebb5bc7c8fed78aL, 0x4e15d87beb7259L, 0x9e9c5bd8f98d626L, 0x37f2120a5250bf9fL, 0x350b5098d6007da1L, 0x31994d0dea8bfdfL, 0xf066730ee502429cL, 0xa1b90ef0f2fdb751L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 59;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x5853e4c4363186acL, 0x68f237d16fb3664L, 0x6f5ae714ff0b9346L, 0xa9d89488a059c142L, 0xc0bc0e569192408L, 0x47b864fae14e7b1cL, 0x2ec4a76681828876L, 0xe2d87d2363c52f98L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x863adcbfc3e11936L, 0x132997833c5875bdL, 0xc66fb8e48cec6857L, 0xb9ec70c15113985fL, 0x2dbe3b667dc96eebL, 0xcdc946093e60978eL, 0x17495e3dd74c9d3bL, 0x2babf31ff018f49cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xbfe7a7a232b36e90L, 0x9e343d94e0d10f3L, 0x7092b86763c2e444L, 0x5ea782b53ca25e6fL, 0x418b3ae543bda0bL, 0x9c7e053e0f670ec0L, 0x8370cce7d87c9966L, 0x96e900ecf9e095cdL, 0x2de6f7fb8daf928aL, 0xc9a7406255d3f59L, 0x5714d1cf8de0d511L, 0x1013dc38b0b9d71dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 60;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa6eecf308794885eL, 0x74b44206ee3751beL, 0xcc8715abbc82a095L, 0xd5192c88589b69ffL, 0xe9f04cd324c2e311L, 0x6b5df55fe390da5bL, 0xa3f98377daa4c864L, 0xa05a7aa8dd0ce3b4L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe026f5b25f9d77c1L, 0x61b9a701a5f704dfL, 0x2730039c46524a75L, 0x7088827dca75a5cfL, 0x52ef898f672d8f62L, 0xcc5deaa0af391f41L, 0xb7f1ae76b644d202L, 0x1b1ae496616b04f8L, 0x591130ce786b77a2L, 0x8b4bbdf911c8ae41L, 0x3378ea55437d5f6aL, 0x2ae6d377a7649600L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 61;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x53086025107aa7beL, 0x318138d8e4da40ceL, 0xbc52988f4d4885faL, 0xb79be12e9542f5a8L, 0x69fbf9169cac00faL, 0x824b866557bc6482L, 0x1a09a19e05ebf9ecL, 0x73b4c7ff8051c9d8L, 0x1298ffffed66L, 0xffffffffffffffffL, 0xffffed6700000000L, 0x1299L};
uint64_t A[8] = {0x7306bbb8a15a8e04L, 0x8f02d66c01def11dL, 0xd63291c8154a67e9L, 0x7c6e85f3616f1ccfL, 0x1e787b17c6e02971L, 0xa4194c68b7b0ee5aL, 0x48bb709e959aa2bcL, 0xdc645794566e4359L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xed5daa4ae6904078L, 0x712bd14734ebf65L, 0xb6eacdbd7c109946L, 0xbcaf8130be55c12cL, 0x4965aeb158564c8bL, 0x9d8a7ad5cd659edaL, 0xe126541937bebd65L, 0x17956ef0cc74dcbfL, 0xece4fa4ee60050ceL, 0x60b90b183c6723f9L, 0x10b23630523c649bL, 0xe0bd85d75dadf2acL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 62;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf2ce78da527b0e23L, 0xef4971c55d204279L, 0x2138ca7dc35846f5L, 0x10d3f742d32f4260L, 0xa196238134f62855L, 0x8023537a7dec4dc0L, 0xd26539b4d7066b9fL, 0xf6021f19f18408c0L, 0xea42b722155ca0aaL, 0xffffffffff9f57cdL, 0x155ca0ab00000000L, 0x60a832eaa35f55L};
uint64_t A[8] = {0x694ee4e9a8bd4f9dL, 0x77d335e552e3660cL, 0x523ce279ea653c2dL, 0xa16534739bad9f30L, 0x41c4e903744eda68L, 0x45a5457f2ba7c27fL, 0x578aa86076fcc7beL, 0x9a49e32de56a12e6L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x86c855cb1ad210feL, 0xf4d61762133be39aL, 0x3d335082428b3877L, 0xcc852c1cd074a99fL, 0x9b86f47ecb475745L, 0xcf6f331f2e3b4c33L, 0x2d1a1a5d10a82dc0L, 0x1b7ec7cf72590b16L, 0xfb70686b7c234542L, 0x1d899b7bc1351560L, 0xf9f61f62bc57b978L, 0x9fe763fde3584d5L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 63;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x78ed4fe6e3a7de48L, 0x5a7e384de42f8cb2L, 0xa3cfa7fd44b81977L, 0xc7c6e4d1c4ce250fL, 0xb12347993e909dfbL, 0x9c03344b75554fadL, 0x55912064d0f5bb2aL, 0xa9231c8ce9e571caL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x9327b0e9666b1242L, 0xf5f3ebfb4d392c57L, 0x7304174a87d08095L, 0x6869c3bcf7e94bb7L, 0xc3c5a8ebeeb43c51L, 0x3ce9943ebc307220L, 0x8fe1ecf0cfcb6406L, 0x710e6e6b5594a88L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe872e42f6df8fac7L, 0xaf049c1e66163e68L, 0xeaf45e5014af53b4L, 0xca799cdcf531a42aL, 0xa4945e1d12f7b61dL, 0xa68f201f9a391eL, 0xbebbea65daae5414L, 0xfdc3f1a5b5c9f00eL, 0x1a3a610282c333faL, 0x9b75b3ad69099fa4L, 0xcf346f4d4318671dL, 0xa0a2deeb331b26a8L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 64;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xddd8babd27088fdaL, 0x8542a97638fa869L, 0xfcc2dcb2063ac9a0L, 0x518f401c863df214L, 0xb9479af3326085f1L, 0x62189a505f42d14fL, 0xbb06f07dbfb93f4L, 0xfa1523624d7ee608L, 0xe6a8ffff1956L, 0xffffffffffffffffL, 0xffff195700000000L, 0xe6a9L};
uint64_t A[8] = {0x694ee4e9a8bd4f9dL, 0x77d335e552e3660cL, 0x523ce279ea653c2dL, 0xa16534739bad9f30L, 0x41c4e903744eda68L, 0x45a5457f2ba7c27fL, 0x578aa86076fcc7beL, 0x9a49e32de56a12e6L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x30aac2385755272L, 0xfa04766b2b49e87aL, 0x25c66aa2764b133dL, 0x86de06685c1a595aL, 0xfbafa03bac23f72cL, 0x1ff3c7e9e625ed06L, 0x9bc84b2ed87893d0L, 0xbd9519a1d13a1f70L, 0x5560ba8602f86b05L, 0xd76fd78cf646a517L, 0x62dc250c0f5cf166L, 0x54ba048d775c777eL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 65;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xcc3024b2d40b5deL, 0xb0f51512b5ec36dcL, 0x6e9724d8d9e2abb6L, 0xdf3b835ee596ec66L, 0xeb8e7dcb084f122eL, 0xcbecf3c1a122f71cL, 0xfb7bc7abac294efbL, 0x8f775c4a59aa43c0L, 0x5b9c0d0fa463f2eL, 0xffffffffffffffffL, 0xfa463f2f00000000L, 0x5b9c0d1L};
uint64_t A[8] = {0xbdc3f5804558c906L, 0xbe50b32eac05abe5L, 0xabf8eec667de9f04L, 0x30c099e05035eac8L, 0xc2a65a2b6251ee57L, 0xaa1010f7e96e7986L, 0x9f80c4fdf2efb104L, 0x22e94574db40cdfaL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x806c79484d0bb101L, 0x64b19eb02b77c7e7L, 0xecfaf1fea8a5acccL, 0xc4d10f9e6259f131L, 0x54d2f34392478453L, 0x388300b14bfe1e16L, 0x44ec26332754a171L, 0xd5846eaaffb7d7faL, 0xb9c30debf63b2252L, 0x84eb328a18a97e46L, 0x55c60fe5e0216e8fL, 0xa59633c86ca1cfafL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 66;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2748b4b97246f4c7L, 0x10cfb0375586a4d1L, 0x34732fde901a955dL, 0x396151f4481d78ffL, 0x53b159f481101c07L, 0x4e2e75073742b608L, 0xfb8bb128af1b0b20L, 0xf9464d607cbc6a2L, 0x8b98afff74674L, 0xffffffffffffffffL, 0xfff7467500000000L, 0x8b98bL};
uint64_t A[8] = {0x47b8c90e0ec452b0L, 0x8691f46ed9af1fa9L, 0xda120f3433f2d27eL, 0x160837d249afa40L, 0xe0053424c4c03fc6L, 0xabd0d5874b2e52adL, 0xe28134da897595edL, 0xc9d2fe827d859fdcL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4323cc9909e903d5L, 0xf22e7e7a0c828736L, 0x2baafb35e732808bL, 0xb9901b8a969fe03bL, 0x4d5b5ec7b70a8693L, 0x6280394511d54ce7L, 0x3b9e187046ee78d3L, 0xa25198005ed2b5f8L, 0x40404cf50687fb6eL, 0x418a166b31cd3a2dL, 0xa3dc0939f88de91eL, 0x638820323284adb5L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 67;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8419b973bc08555L, 0xd4c30af602e13740L, 0x3e8ab4ec95fae4dL, 0x931e75dea8586108L, 0x13eaa868192dbfdfL, 0x40ccccd5cc83e9ecL, 0x473820ee0985ef50L, 0x7331ad4b74eacef3L, 0x1b8fffffe46fL, 0xffffffffffffffffL, 0xffffe47000000000L, 0x1b90L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
// J nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8419b973bc08555L, 0xd4c30af602e13740L, 0x3e8ab4ec95fae4dL, 0x931e75dea8586108L, 0x13eaa868192dbfdfL, 0x40ccccd5cc83e9ecL, 0x473820ee0985ef50L, 0x7331ad4b74eacef3L, 0x1b8fffffe46fL, 0xffffffffffffffffL, 0xffffe47000000000L, 0x1b90L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 68;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x38c528ce9d842325L, 0x97f6b0670b856664L, 0xa017b205b516329fL, 0xf7b4d8b2c2bd0204L, 0x63e5f5faacc61207L, 0x9638fb341ef0d04bL, 0xb33515f039489987L, 0x76f2c6bd24209a14L, 0x3fffffffbfffL, 0xffffffffffffffffL, 0xffffc00000000000L, 0x4000L};
uint64_t A[8] = {0x7b772ba19675c72fL, 0x42b5ecb89f2ca919L, 0x174ff317bb1c31fcL, 0xc2968078290558efL, 0x838dc8f4b124d3f9L, 0x215c5b2972a94e5fL, 0xfb0576da94b935L, 0x2e2a1e582c01dee7L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3cf688066b0cb5f7L, 0x5bdeef984453e266L, 0x36f165fe079f768dL, 0x818e957bdfdc5786L, 0x2ef9a16a757a01dL, 0x44b3ebd3d1300ddfL, 0xba2923db42c0eb46L, 0xb37cb5aafa160e02L, 0x69978dd1f23b0269L, 0x68aa17be63334f8L, 0xa7980baecd59e2b6L, 0xdf370d3e9c2d7a16L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 69;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xeffd0fc448c7d559L, 0xc83278174227a7d8L, 0xd53bbaacc1f01d51L, 0x63440d7985bc99e7L, 0xd0116bd33dfe3217L, 0xdcb5dc5e4b95356dL, 0x8d83ef960d545f28L, 0x6bcf2b48b202ce9eL, 0x6f300e9290cfef29L, 0xfffffffffffffdbcL, 0x90cfef2a00000000L, 0x2436f3010d6L};
uint64_t A[8] = {0x1b8e99ec73674fd0L, 0xdd2db1ac1c655c22L, 0x6961af51e2d8306bL, 0x8be27de7f56e210fL, 0xfb1256c27d874a2eL, 0x16f5d1e9cfdaa431L, 0x8fc19cbb4701173dL, 0xfbfe9539b70e2b92L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x84f551f505eb2437L, 0x5f7c45c4190d72c1L, 0xd6176386cf4ee670L, 0xea0cbd27819c4f76L, 0x775be5aa10c0f359L, 0xf6c8ee0d1c8c8a20L, 0x4cf655b6c17d3727L, 0x9297ff61c838e6b2L, 0x79ce472f2952c638L, 0x65a5bcd0f70018dbL, 0x498cf84ca642dac9L, 0xc96607a4fbee327L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 70;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x262deb66c1034417L, 0x3bbef1f9704f25c0L, 0xfbb1370c9e39d7b9L, 0xeac8c72b27688676L, 0xfaf6786f7636a406L, 0xcf827b1840ab3660L, 0xe950c06cf746c0d2L, 0xcfbfe4e6ec6966ddL, 0x5effffffa0L, 0xffffffffffffffffL, 0xffffffa100000000L, 0x5fL};
uint64_t A[8] = {0x34388d1781c06c9fL, 0x6bab4b917ad416d4L, 0x69e8676b0f741fb9L, 0x644183540e13bc56L, 0xc9e365086ce5a54dL, 0x25a1220971c2ab59L, 0x6b3a5852142b9a43L, 0xaa73fe0d6ef970d3L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb88d4f6fbdd3205eL, 0x445a9da0173f2690L, 0x461cded1cbfdcb34L, 0x89406f986669fd2eL, 0x957f89b411867d0aL, 0x57352c1ef31fca57L, 0x70acc6f11b4e4ec6L, 0x7ee99730930fec52L, 0xf595ea406315c317L, 0xc17886e5c0f88e98L, 0xbd49fe534a9d1602L, 0xe779a52436da1bfL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 71;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4b8273ae870397f0L, 0xa68bda6b00afc30aL, 0x220fec94af5c774dL, 0x8acaf026e380403bL, 0xf61c04dbb8afb88eL, 0x449888db200b887L, 0xe51687e350499758L, 0xfc29ef1b198b43f7L, 0x5d1087d6a2ef7685L, 0xfffffffffffffe5cL, 0xa2ef768600000000L, 0x1a35d10897aL};
uint64_t A[8] = {0xc9a5bd13954b9ca2L, 0x566feeb4d61328caL, 0xcfd7bf48e54e1acdL, 0xeb2603b57b7acd4dL, 0x7bcdd0ff094f23f1L, 0xcb8721ecb3ec12b9L, 0x9e4cbd67c300f661L, 0x31ccefd32ba4dc4cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4d8b6c0c0c3d868cL, 0x43eb03c34119e45L, 0x9df9a8e47c5a3addL, 0xb6807824bd93ded8L, 0xbe82eb3600620ee1L, 0xbb1b185deda109e0L, 0x22bb48b1327bb7e7L, 0xd452735868602d5bL, 0x37dfec7f8db72895L, 0xb10c65acf79320f9L, 0xbb5e890e3b8ff8e9L, 0x2bd8bbe506d580fcL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 72;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xb098e6b2eb6f685fL, 0x2f7980537bf3a01dL, 0x109d7c254267e3d1L, 0x3cfbb35266406e49L, 0xf66feef6b468edc7L, 0x8507f2ab800c0450L, 0x28a59deab44b4a31L, 0x818a3bd4b3095a04L, 0xa73c567851abcf8cL, 0xfffffffff8e82605L, 0x51abcf8d00000000L, 0x717d9faae543073L};
uint64_t A[8] = {0xf9e52a3c3d09587fL, 0x4df9d7e007e02f99L, 0x56b54f114a88d0ffL, 0x8bd26aa0267ffedfL, 0x28abcab71f0d0a08L, 0x41011586e26e500fL, 0x117b7425690e41d3L, 0x1877d8811bda67eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x339ee28fe3441e2eL, 0xe0a94afb5cee01ddL, 0xf9a77991d9dcfceL, 0xa8df2dc7b5353441L, 0xbab6aea9f6749477L, 0x92eff99e19ded246L, 0x48c485af9fada162L, 0x4ba6457a4cb291ecL, 0x4482d2bfea3ae299L, 0x40d04d8f04ddfecdL, 0x9ab36d0b0de0bdd4L, 0x345970777770d2c1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 73;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xad059e61fa2a7e83L, 0x868891e9ae098798L, 0x6a53ec48fe259e5dL, 0xa11cc5e7934749d3L, 0xfac1a76fcbb3eefbL, 0x553a8dd1269bea0dL, 0xeb91e204f987b06L, 0x87f4eb5cf66d37b1L, 0xfffffffeffL, 0xffffffffffffffffL, 0xffffff0000000000L, 0x100L};
uint64_t A[8] = {0x49b2a0b16a395853L, 0x32092e494617dd75L, 0xce614c2f83c516f2L, 0x40afd261d2a96d7dL, 0x735fd9b0767a558dL, 0x7c83d9d9520a759fL, 0xf34063ae496cce27L, 0x4270a2bd4b257a7aL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xc9436da3d4bd117cL, 0x3b1ba63326d3afcL, 0x2c26d12b3c4e7788L, 0xd72cf971a55f73bfL, 0x9f5171b02da8025aL, 0x62027803d6a0b7c1L, 0xc796c8be464fe514L, 0x42ed56bbbe0199daL, 0xac1589512869d3b4L, 0xc0b42e2f6c46c8e1L, 0xdb4dca25cca25231L, 0x450cc1da35ffdef3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 74;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x56ec4ad11d01e7e7L, 0xada201817cef118cL, 0x986ab7cc598976eaL, 0x9ea7e065585a7f79L, 0x942ae6dfbfdc8deeL, 0x14f52efecc39b364L, 0x9ca63affa32e2733L, 0x387eedabdb7ea5dcL, 0xd23fffff2dbL, 0xffffffffffffffffL, 0xfffff2dc00000000L, 0xd24L};
uint64_t A[8] = {0xd4132c949782a702L, 0xb9c7481ab24decfcL, 0x1c1aea428adc92aaL, 0x700b7340f3884e72L, 0x7400a35dd27a2b5aL, 0x65444adb78515317L, 0x9866c40489564d2eL, 0x599c5f75dc920771L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xd1bf6ccaf9b2530cL, 0xa55e692c5a28814cL, 0x896d9a3817b22e4fL, 0x53e5bc04710de19bL, 0xa7352cc75de33b7dL, 0xe41c7283202e60d6L, 0xd78bc6ace46c8d3aL, 0xcb68e24c5e74a5acL, 0x2172afe8a7782b39L, 0x11e76a879dfa97ddL, 0x14df04aed59cb185L, 0xa907ff8b5e466d37L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 75;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x9bb52c106d6fc482L, 0xf00045208d424ce7L, 0x133f022e360c6e5cL, 0xbe81c6bce347c41aL, 0x3e58cb7a88efcfe2L, 0xd078b58191820c29L, 0xb7acf095bb4afe86L, 0x7f20a3010136f582L, 0x5f5e0fffa0a1eL, 0xffffffffffffffffL, 0xfffa0a1f00000000L, 0x5f5e1L};
uint64_t A[8] = {0x2d0f1be2b5577cf9L, 0x8decdf26c01ce141L, 0x7e28a0d562d7881L, 0x8218884b2f38e1d6L, 0x707320391e7826faL, 0x36925b3cb704a1fcL, 0xe77da7d78929b20aL, 0x747c0826cd4f4e7bL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6866d967edb7483cL, 0xe55656854d48bac5L, 0xdf5d903c296c67c8L, 0x92ce29c970dc24fcL, 0x4df54bcda51bd519L, 0x16dcf0eb4d5f6105L, 0x3bd10b047dcc2f68L, 0x7f57e0b66a56e39bL, 0xa2c3d32686d8c816L, 0xd05869f491d6c1a3L, 0xb5a13afba087e357L, 0x583d1a50953bfe02L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 76;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x649c89ce5bfafe43L, 0xc2e2594c30a92f8fL, 0xa155cbe31da6a5c7L, 0x5fb35ccfed2bad01L, 0xf3a8cfe389bc7d3dL, 0x4b00b20b906014cfL, 0x9b359611f32c50aeL, 0xd158667de9ff257aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xff25a17d7870dc43L, 0x2882a3ad091ad8f4L, 0x86422227a32da1f4L, 0x5a90d00864bcd653L, 0x4879cd108c355101L, 0x8ded40b9d62f9fa3L, 0x2ecaba53bc0387efL, 0xafc51e23e464bb1cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x64a616e7661ef7f6L, 0x845241efede05a3fL, 0x261a260396b6cac8L, 0xcf3ef9d1358a0d26L, 0x51e98af464fbdbd0L, 0x3f6fa2c187b35a00L, 0x15d57ba4c00ef9acL, 0x89b24b42436b36eaL, 0x9a8917af1c75ddffL, 0x65a04a60d871a964L, 0xe4ec56448586fc2cL, 0xfadd733877912952L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 77;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc2ee33fce1548c96L, 0x42b53da83c79201bL, 0x932ccb6bcfa7e0dcL, 0xc9a4c3aea2e42c6bL, 0x73f32ab8518a62e8L, 0xa76d9d98ae476cd1L, 0x6ff9d31d8847a372L, 0x62c5b7ef6d7550dL, 0xf423ffff0bdbfL, 0xffffffffffffffffL, 0xfff0bdc000000000L, 0xf4240L};
uint64_t A[8] = {0x1e2d270d1f79fb85L, 0xc12e67b45d047997L, 0xfaedd341f1e746fbL, 0x22e78b4130420919L, 0x4c96007e85769ceeL, 0x1d0112632023af99L, 0xad0d5d48053af2f2L, 0x819324322cf5f440L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x658df34b0fa47ba3L, 0x9668d208be5924bcL, 0xadf857500f21b485L, 0x9d0e797d3a8a8248L, 0xaf81f7f880d84f77L, 0xfbd9071ab02177e6L, 0xb575b8a76fc1f76aL, 0xf3ec64090065f4d1L, 0x57f1d1f6fc0f84eeL, 0x7c5ea1cf23b7a148L, 0x968f3e9c5c620595L, 0x7e395b36d4bd160cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 78;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x5131ef687d429962L, 0x96319631d2a1773L, 0x3f1e2278e33bce30L, 0x6177a09364111f49L, 0xff7a81f5697c1e38L, 0x3fbf69e8b3bf7480L, 0x35963ecf6ecff003L, 0x40b727ba807509f1L, 0xf517544e0ae8ab3bL, 0xffffffffffffff8aL, 0xae8ab3c00000000L, 0x75f51754c4L};
uint64_t A[8] = {0xb595d8a9eae3eff3L, 0x1fbf14715b64ea48L, 0x2c1fa02b57ccd532L, 0x13ad0573e9799e4fL, 0x9026eb180cd032a2L, 0x82128bb46643b150L, 0x818a6d8f4706304cL, 0xd93ef16f097c5ad9L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1f0c43b716af1329L, 0x7ea87d7f4d826e74L, 0xb61ab259484902eL, 0x1595882f5af4dc6fL, 0xeaf2b079360080fcL, 0xf18a606eda333abcL, 0xaf7df76777f90dcL, 0x34f20fff94b6026bL, 0xa6839beaa0eb9f2dL, 0xfc2a698961288cdbL, 0xfc9f4f032aa04126L, 0xce9969433d14aec4L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 79;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc7d8a2c8f27d12baL, 0x6745af5b6052bd66L, 0x3f2f7e75ae50f0f8L, 0x1bc13d1704d56e1fL, 0x8537c7902d3eaa4bL, 0xa233eaa511b0a6c5L, 0x6e66d5142b74a827L, 0x349c07b796f9bf4cL, 0xbc5a1e3f43a5e144L, 0xffffffffffffff84L, 0x43a5e14500000000L, 0x7bbc5a1ebbL};
uint64_t A[8] = {0xd18d9b0f700e5cc0L, 0xf69a7d30c2cce0c0L, 0x1f352382f17659e4L, 0xd361c63157c3aa13L, 0xa5ffb367f0ebeb65L, 0xfa30d2ada9eaf6e1L, 0xe95de0b741063f0dL, 0x4aac66d83f3f4b6eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x55cfb8a5a2243e15L, 0xe49156de4da5a142L, 0x7bbabeefd8e2be98L, 0xa5764e744284381bL, 0xebc37e46511210f8L, 0xbef296c81cc55759L, 0x94f294ea295e7152L, 0x1974a84c9618a2eaL, 0x2d6ed1128bb3eaa7L, 0xd445f613dd595d2cL, 0x1d128d3982f4630cL, 0xc9a483d22a739da7L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 80;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6b703cc03eb88876L, 0x36646f5ae714a6b7L, 0xae821b539488a059L, 0xc1425853e4c48e85L, 0xd189031c29962e7eL, 0xc4a7667576c7916dL, 0xb39835b3c52f980cL, 0xbc0e57524e4edb0L, 0xfffffffeffffffL, 0xffffffffffffffffL, 0xff00000000000000L, 0x1000000L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x2f89ce3fdb43e874L, 0x59442cd71969c97dL, 0x2f5574d8d91f145dL, 0x2922031e34ef4181L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x45501e05fd481a04L, 0xb295bdf6409a91bcL, 0x84f4265e43247032L, 0xabfacc69c6a63ce0L, 0x3201b5798ac107f9L, 0x96ea7180ec9663f3L, 0x18545f01f119f48dL, 0xf464baad3fc099e9L, 0x3f55d73a8a350bcdL, 0xa518eb5948517de4L, 0xacd6e79ca63ebda7L, 0xac1b3b717a948fc3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 81;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2bd0204360826caaL, 0x41252997f6b0670L, 0xb856664a2d4b409bL, 0x516329ff7b4d8b2cL, 0xaf490825d5cff157L, 0xa8f439ab06e58e3eL, 0xcd07bc34c235d56cL, 0x10e522661ddbcb1L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x1b8e99ec73674fd0L, 0xdd2db1ac1c655c22L, 0x6961af51e2d8306bL, 0x8be27de7f56e210fL, 0xfb1256c27d874a2eL, 0x16f5d1e9cfdaa431L, 0x8fc19cbb4701173dL, 0xfbfe9539b70e2b92L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7ef384e79deac439L, 0xfe39113e1c2a67bL, 0xa1bc885a03596e5aL, 0xabe2a6433a396548L, 0x204f51ccb68dfdeaL, 0xeaafdfc99be342f7L, 0xa80223aa3a36ba74L, 0x778496ef4c1221f1L, 0xefbe79a812e4e327L, 0xd91b5f129cfa55b1L, 0xb10b4908b58cefd0L, 0x3a7f53e87a2095e2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 82;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe97f6611b1cda5bbL, 0xb10f2987f83f9aa6L, 0x81e5d3e898193812L, 0x267df4b457c43fe6L, 0x6bd4602c199315bfL, 0x687d348bca97859dL, 0x38a6238c79349b0fL, 0xc8bd81b74891bf56L, 0x4effffffb0L, 0xffffffffffffffffL, 0xffffffb100000000L, 0x4fL};
uint64_t A[8] = {0xc2591a80f7fe3f88L, 0x554c2c0348e4f302L, 0x3b1995c38f8c65c9L, 0xc79e9e572406569fL, 0xb28666dac04097cfL, 0xb79f9675cb6eadbeL, 0xf67ef719e7a2a9beL, 0x5f100402249c2c7dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcbaa8f1d98b27e72L, 0x28e0eb2e2656e536L, 0x6eef196a20f40d11L, 0x7df303adcf8b11c0L, 0x1bad52b4a6066fccL, 0xca8e113b23bbb87fL, 0xa83caf859eac99e9L, 0x75f26c4ee39b99b6L, 0x6730bd917b9d9eecL, 0xc563f93d096dec1aL, 0x7a183d61cdb103d3L, 0x38dc919735ba774cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 83;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xcb5f21848b153494L, 0x43e937164a6ef82aL, 0xbabc08cbc78d2388L, 0x9ea08c3be1207b32L, 0x20df3edb735b1bL, 0xeee81029724f8550L, 0x3d6917173bc00f19L, 0xb038cd8ad903a14fL, 0xf18ffffe1bb699e9L, 0xffffffff0d4699e8L, 0x1bb699ea00000000L, 0xf2b96617e4496616L};
uint64_t A[8] = {0xa7723ce1e1403180L, 0x9264d3dcd3659124L, 0x9b429deaa6e3608aL, 0x138769c2d77cb7d7L, 0x7cfac5ddc9bc8e59L, 0xffa0d620bc76856cL, 0xad33546206ded84eL, 0x2471b4adeba2b03eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x388ca861631d7c57L, 0x893f78b4eff59b10L, 0x986a6f9224bc88f2L, 0x99398f72dad0ea9fL, 0x3933c095fd2f5c76L, 0xe971c57dfb8c0118L, 0xdcbd903832d9da20L, 0xab01877516bac0edL, 0x1585b7da386eb87L, 0x1e6e5412a5e2feb4L, 0xe812f651f2d19122L, 0xa10055d4dc54a37aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 84;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xb904efe450803ee7L, 0x97d3d28fede6df03L, 0xcb46dde71e00677bL, 0xb8e51cae1d0b9c3fL, 0x97c8eaa2d19c479dL, 0x564e71345faa5b7bL, 0xd73048af79822eaeL, 0xa00c8eba9d727767L, 0x2fa27fffd05d7L, 0xffffffffffffffffL, 0xfffd05d800000000L, 0x2fa28L};
uint64_t A[8] = {0x7306bbb8a15a8e04L, 0x8f02d66c01def11dL, 0xd63291c8154a67e9L, 0x7c6e85f3616f1ccfL, 0x1e787b17c6e02971L, 0xa4194c68b7b0ee5aL, 0x48bb709e959aa2bcL, 0xdc645794566e4359L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x50210215f6be5e0fL, 0xc616788ae3f0026cL, 0xc45a1c62ff3d53adL, 0xc0959df2e145ca27L, 0xee67114e35f31f37L, 0xcf2f0f30ede496b3L, 0x975dbc8704b2ff91L, 0xc1e21bd28b0053afL, 0x5259517995dc5917L, 0xc63afa7f799ad478L, 0xc2f2e3c2363b07b0L, 0xc04916ea65603c2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 85;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xac7fd179b754b796L, 0x8d2cfe2585b941faL, 0x8f4e09310eb9b1cbL, 0x8db28655da12296aL, 0x2f82222a9f19f922L, 0x2117c0e8d75d03baL, 0xbba92730bccf25acL, 0x8f7bd3e6ef15e242L, 0x3bd5ee0fc42a11eL, 0xffffffffffffffffL, 0xfc42a11f00000000L, 0x3bd5ee1L};
uint64_t A[8] = {0x3ef7fe59ea3221baL, 0x32b0a08a947eb0fcL, 0x14e3248935cb57a7L, 0x4b58c0845c0e281bL, 0x2bba72ad6d2715cL, 0xc55188170fd69b7eL, 0xf77dd00bfc38ed37L, 0x6f3fc230de80a5dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe66d29357ec1dc93L, 0xa96ca631c7f5964aL, 0x5be67f5761d0563L, 0xd2e8a9417c0a9fa8L, 0x867bba45598bc63bL, 0xa188ce8eb2abf0c9L, 0xf988cefee2373158L, 0x5b9d3ece3c3efa51L, 0xc1ebf049ee31e9efL, 0xfa090ae298d9dc34L, 0xb38b9a0357bbf62L, 0xc7c9548b4f3b69f9L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 86;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x54d63c809103b723L, 0xd5ef2f7c2c83f549L, 0x5882e0753ffe2e6bL, 0x808b0b650bc6fb80L, 0x64edf7b201efe220L, 0x55c4623bb1580e9eL, 0x3670c3194b0b6587L, 0xf2f11bd652a23f9bL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xe22b104ad0f67420L, 0xbaf5500801638fa6L, 0xfe4601e2b5bf98aaL, 0xb2e97c5f8d1e0c72L, 0xa09a2ad2d0d67a2fL, 0xcf3cbad5d5c143a6L, 0x57b4042b9fcef2dcL, 0x2b55741691d9fe6fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x70669f98a0245e40L, 0x4a42a84442425badL, 0x447307d5d52cd667L, 0xbd3ca0d66de0cd09L, 0x1fc3f1f757c048d0L, 0xf881968babb763d6L, 0x7e3934a5bc2491d6L, 0x72f08d68b533f3e2L, 0x8d54d3ca3ff2bcfcL, 0xe506208bd4df9a5dL, 0xa5c3216d75c16a3fL, 0x325e70fa815710f2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 87;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xbfa1ff3a40551eb1L, 0xd2886384ebcb6ed1L, 0x8bfb80c325f10049L, 0xa52e4e5e6cb94aa2L, 0xaa3e25f1466bd9dcL, 0xe29678a6291c4675L, 0x2464e23ce704dc62L, 0x7aab07488d5c3830L, 0x8be7ca6874170bd6L, 0xfffffffffffed63fL, 0x74170bd700000000L, 0x129c08be8f429L};
uint64_t A[8] = {0x7b772ba19675c72fL, 0x42b5ecb89f2ca919L, 0x174ff317bb1c31fcL, 0xc2968078290558efL, 0x838dc8f4b124d3f9L, 0x215c5b2972a94e5fL, 0xfb0576da94b935L, 0x2e2a1e582c01dee7L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xfb0b4a6fb8415eacL, 0x571267d4dd3ea41eL, 0x70735bfe09890effL, 0x82469ec34a6c4396L, 0x45bf22dcff6ef700L, 0xc881aa067cbe2818L, 0xbb8ca5f6ce9cbf92L, 0x3c0fcd1ddd37d666L, 0xd9eb671d129e94ebL, 0x3042146c6ead4509L, 0x6b155c513eb4e33aL, 0x7518a700cfed34f1L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 88;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x3db9e7799cbf7b65L, 0xf572386de907ebc5L, 0x6fb158cc3a903d78L, 0x182b58c2d9560bc6L, 0x883964029c95980bL, 0x6058e1e208965903L, 0x36e41e8a9dcbe8f8L, 0x5a4b34d061126ba2L, 0x19a0ffffe65eL, 0xffffffffffffffffL, 0xffffe65f00000000L, 0x19a1L};
uint64_t A[8] = {0x5da30e809bf1f538L, 0xbe5d744b3a90ab99L, 0x9434dd7251db0f1bL, 0xed877b75c958ef7cL, 0xafe213dbf0592657L, 0x9805f40db8d4bce3L, 0x1253471881081adbL, 0xed43c8beb572b391L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xde8f9ee99d92a256L, 0xcb4723187dcb28f8L, 0xe67fc5aef1313b8fL, 0x1ee8ee190429a313L, 0xd1a04dbcefdc9597L, 0xfdb7d6dcc023b1f9L, 0xf1a0aec95b3d8966L, 0x4d4bb18ebf968ee9L, 0x374b23f4cb3b300aL, 0x90b8ab30e90424f5L, 0x472d12a29a21f6aaL, 0x98ee8b4403fe997aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 89;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8b72c8c16c4b058eL, 0x37eeba93aba32cd4L, 0xfe0a46807985418eL, 0xa096a029b6b64a75L, 0x5ace6098ec9eda0fL, 0x5af00941bf76b8b8L, 0xb828216361bb707dL, 0xf453d8c8796cd53dL, 0x1fa3ffffe05bL, 0xffffffffffffffffL, 0xffffe05c00000000L, 0x1fa4L};
uint64_t A[8] = {0xc7ddf7864ac64482L, 0x80cb53c4c9ac79e0L, 0xb47cc1f1216cd550L, 0x1df4d36fc0aec63fL, 0x7c792a6f445611f5L, 0x7002065a567a0793L, 0x817c6261de6732b9L, 0x753e20a3ae511746L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x632deee4f7637d15L, 0x73d2f16f2a1325f4L, 0x769f06b73b5cfa01L, 0x38881b9e4131a64eL, 0x69fb61d179da42a8L, 0xad095f7d76ddc4caL, 0x17e87180528c5355L, 0xc1bd323db7632a20L, 0xeabd9ebdab51424cL, 0x2646b78c7fec8ae1L, 0x78b4f57f58b25cc3L, 0xadba45917fa4de3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 90;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x9154b29791225aa0L, 0x42d70f34cdc735a9L, 0xbe3f1f18feb49f8aL, 0xa54bce826cb578caL, 0x5aaf2d24363734ddL, 0xef8c71c92003a5afL, 0x36b4030369058eeeL, 0x9a05e3af3979400dL, 0xfffffffeffffff00L, 0xfffffffffffffeffL, 0xffffff0100000000L, 0x100000000ffL};
uint64_t A[8] = {0xb5cffedf0790a013L, 0xf1ba0f6e25458e39L, 0x66d546ad56e03b9bL, 0x7ce0061255f79ecfL, 0x7c2da8ba0847c739L, 0xc641e310a7eb8838L, 0xf3cc871d693e2a73L, 0x16439c6cd3b5b4e4L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x65562d03c616d301L, 0x6105e9aa17db0176L, 0x3943e570b9458552L, 0x22ab12efefa05cfcL, 0x21fe3c02b6eab1a7L, 0x739d66f718f82bd4L, 0xe8af1cb621fefbf3L, 0xed87fbd5c0b4cc34L, 0x50c18261a8e343f2L, 0xf489d5a8e03d9481L, 0xee67addd93eede32L, 0x3d80801e2cae977cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 91;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc79a356750493688L, 0xc13127e39ba9f610L, 0x58375f151dfae2bL, 0xd7b35dcbad6098a4L, 0xe5d9539220fa5f47L, 0x8a29540182b84ed9L, 0x7b037287b02fc67fL, 0x496b3bdc50f4eec5L, 0xc46bedff3b9411fL, 0xffffffffffffffffL, 0xf3b9412000000000L, 0xc46bee0L};
uint64_t A[8] = {0x76b85af13143ff6L, 0x25e08eed9e9aa27fL, 0x3e3d0488ffc51120L, 0xf8c81b242528c884L, 0x418e685027128311L, 0x63ac37d528a681efL, 0xf0a07a9732ef1690L, 0xc7fe6aa567d1367fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xefbf9e88ee997589L, 0xc28cfb24a5ac6837L, 0xf44454a79e9e3ab7L, 0xfad6573257692615L, 0x3defd5c5c5868447L, 0xb094efeb457af548L, 0x439ee7ae70f3a8c5L, 0xa8e013a2a255d23L, 0x5b0d20cbd03358f9L, 0x82c17e949a1e5827L, 0x41bb0ebded5f94d7L, 0x7e4499bdbf2e69cdL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 92;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf3ade4ec8370378bL, 0x4c484275c47da45L, 0xf73ed514be262625L, 0x95058faf0f8fc7afL, 0xcf50d1e305d134c1L, 0x63e3c2e57bfb68daL, 0x57c8285618afe896L, 0xc7d39d5608647180L, 0xcd7deb7f32820486L, 0xfffffffffffff006L, 0x3282048700000000L, 0xff9cd7dfb79L};
uint64_t A[8] = {0xbc2905fdc2c72f52L, 0x67f5f05fcd47bd28L, 0xc4a70bcc9535ceL, 0xea9479cf0f52d533L, 0x4ef0c2e2a7fb0657L, 0x5d1379f69267bcedL, 0xcc5ccf9a29159b0eL, 0x6febb404d5e365f5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xdccbd80dc90e17fcL, 0x54dff9caa1b46e2cL, 0x2fe6041a5dc04ae2L, 0xfac33780fbed87b4L, 0xbd1e416b7e24d22eL, 0x48862ae1adc4804fL, 0xb9b2bafa908557dL, 0x60f0788505797484L, 0x48016f6a0f177aafL, 0x41212077625acf35L, 0x956b5fffd42e7c48L, 0x914d9acdeb0c27cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 93;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x827427a03fa59b4bL, 0xd18be898101d9b9eL, 0x6c5759f29cf9c8dL, 0x97fd53e2e7a0ba0eL, 0xaf8d462aa65e486cL, 0xa27b5b572996da50L, 0xe9116cf861f3cf7eL, 0xa18da286a0c00497L, 0xfffffffefffffff0L, 0xffffffffffffffefL, 0xfffffff100000000L, 0x100000000fL};
uint64_t A[8] = {0x8942b27f550d6f9eL, 0x8e975fe69f49297cL, 0xc75267ab5e2a0afaL, 0xf3dbb029e1d3b305L, 0x69b85d82f577fbb0L, 0x3ca39341541d3e23L, 0xe8764f91c11037f7L, 0x65a84d585d0ba359L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x9f34231323f227d7L, 0x74707e5014194777L, 0xc7e0780c8c2c17c9L, 0x96d122b898f9f103L, 0x73d5c35f57ba3680L, 0x5002442f10bf80f0L, 0x8205d36f42aec8dfL, 0x8f15e3ca6ca6f7c3L, 0xbbd209c2e8065390L, 0x73adf7784c8965f8L, 0x7880bf7dab52bfb6L, 0x88163d5225b5d03dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 94;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x19daec51b27d7454L, 0x4e0fc7cab5f49a5L, 0xae255f61efa3b090L, 0xc643de7ca0be0ff5L, 0x83eaebc3a088d9e3L, 0x2b781e5bfeead99bL, 0x102fd95053cff706L, 0x4a9436792ea48facL, 0x40ffffffbeL, 0xffffffffffffffffL, 0xffffffbf00000000L, 0x41L};
uint64_t A[8] = {0x2b9131acc0130435L, 0x97a689a71742557cL, 0xa81ea03df9581714L, 0xc34ea0250f6667dcL, 0xd734003dee5d1e66L, 0x7bb0772a8b6e0589L, 0xb1f409df762e3ef3L, 0x60f7817684aa164dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x5023f64c86159ee9L, 0x8598fc9299afb87bL, 0x5aa7a9f3bd4aa962L, 0xb04e868b7365e4e5L, 0x42bb1d6809df9cc4L, 0x70f2f81d3a98f50eL, 0xde4c0b68aeadc932L, 0x1e19d0279f310719L, 0x47e48d581e1b5791L, 0x77d95cb6cbcabfe9L, 0xc69c6472038083beL, 0x25a66ec89edc3631L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 95;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x88b56923125ef590L, 0x9b859cd90fdb31fcL, 0x940b496c16c2318fL, 0xa0d08f39bbce9f43L, 0x6c52cb7ba74e6124L, 0x158ec18727faccedL, 0x46d47892b18b5133L, 0x8529014de0b54e2eL, 0x2dfd3892d1fa7c83L, 0xfffffffffff7b516L, 0xd1fa7c8400000000L, 0x84ae92e05837cL};
uint64_t A[8] = {0x57fcaf64b5e8d6dbL, 0xf670e79ac97efbdcL, 0xe12253fbdb991b94L, 0xa928a6d84768c868L, 0x1d94d6153c3e2656L, 0x2085b6e8694a3819L, 0xea05005e197a2805L, 0x8004d784b244753L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe3e0724baf79f550L, 0x448231d33cd59e3aL, 0xe57b71f576375255L, 0x4a9369b26c1355ccL, 0xb9a95355ff875e5dL, 0xb4510a1eacee97a1L, 0x89200093f5ef824fL, 0xe3da7e101895774dL, 0x9fae7645034b33e7L, 0x3d3c25759979a9d2L, 0x7601177e9bfecd7eL, 0x972c6f631f46a1bdL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 96;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf98c587216e2248bL, 0x26120d2f06dbdf5aL, 0x2371f148615a4130L, 0x98d060a41d35151L, 0xa0c673d585149c62L, 0xf9bbd87d026facfaL, 0xec9ded87a13cab52L, 0xd59fd742e1da671cL, 0x33d495ffc8993413L, 0xfffffffffc6dca13L, 0xc899341400000000L, 0x39235ec3766cbecL};
uint64_t A[8] = {0x34388d1781c06c9fL, 0x6bab4b917ad416d4L, 0x69e8676b0f741fb9L, 0x644183540e13bc56L, 0xc9e365086ce5a54dL, 0x25a1220971c2ab59L, 0x6b3a5852142b9a43L, 0xaa73fe0d6ef970d3L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xd489afe8cb1bd86bL, 0x2b3c343f99612399L, 0x5e18656690d6f22cL, 0x5069e3a46015ffcdL, 0x3ffe3d5ea6dbead5L, 0x18a83370aa8c4608L, 0x9321752f50e360cbL, 0xbf099ec4acfe799cL, 0xf8e89a630446f749L, 0xe77f9f2a7fd462f7L, 0x66e5d3c90c64cfedL, 0x4fb4f0195e9baa30L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 97;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf5d6dd72877f65e5L, 0x13cac83d3e454862L, 0xaae09e064b6511a1L, 0x2092a9da58d958efL, 0x1dd2f7d1993f53d4L, 0xf3b76d8d81a0dc98L, 0x4a4d9f035f3cd456L, 0x82c889d8a617495dL, 0x2adfffffd51ffL, 0xffffffffffffffffL, 0xfffd520000000000L, 0x2ae00L};
uint64_t A[8] = {0xa3a8acdfb4c45f0fL, 0x40633f71dd93c7f0L, 0x12960ebce3bb096cL, 0x63f522c7506af27aL, 0x67f33420ce543d5bL, 0x310f8883245c7fbcL, 0xfbb7fce0856c61dfL, 0xb39ac8d3c824d326L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x319adc5da37c1bc8L, 0x325bf9df736fde15L, 0x83022437be32db68L, 0xc7a2ae1900788397L, 0xeb280fd06b5b64ffL, 0x62838ca774d76619L, 0x8caddc8963ee0627L, 0x34aad16c5229f21bL, 0x86fe2a75332c3882L, 0xf3ab0ce1dc1e6dcbL, 0x16f253987c184710L, 0x99c2753c400ab94bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 98;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6c8086b76d079091L, 0xf74bab292b026c10L, 0xb843e731ed06dcc0L, 0x1ec735457d4e3729L, 0x2e27487210b67067L, 0x3d811b53d1450c88L, 0x69ecfce54d8011baL, 0xcbe6972c8e83693dL, 0x1c9c5dc0e3639d60L, 0xfffffffffffffb21L, 0xe3639d6100000000L, 0x4de1c9c629fL};
uint64_t A[8] = {0xf9e52a3c3d09587fL, 0x4df9d7e007e02f99L, 0x56b54f114a88d0ffL, 0x8bd26aa0267ffedfL, 0x28abcab71f0d0a08L, 0x41011586e26e500fL, 0x117b7425690e41d3L, 0x1877d8811bda67eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x58c52a24bf37a598L, 0xd5ce51a94769c58aL, 0x62b10c024c8341ccL, 0x96effe7709bf553fL, 0xdd4e961f1fcea0a3L, 0x836311e81f9dc680L, 0x668c208000709f7dL, 0x50d2490674ccd613L, 0x17be28001819999L, 0xdfa512fa9ab23872L, 0xc6ee0bff0b3d275eL, 0x2f83920f7d04efadL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 99;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6db39a636f0cbbdfL, 0xd182e2cd8d8b03f0L, 0xf7286f4c74854e0cL, 0xdffc59a35f4f6dd9L, 0x34e083ef1281110L, 0xf6fdf0dee31bec71L, 0xc70c9919ceb61a36L, 0x96d8ede2b8c84d3fL, 0x6e7d348f9182cb6L, 0xffffffffffffffffL, 0xf9182cb700000000L, 0x6e7d349L};
uint64_t A[8] = {0xe22b104ad0f67420L, 0xbaf5500801638fa6L, 0xfe4601e2b5bf98aaL, 0xb2e97c5f8d1e0c72L, 0xa09a2ad2d0d67a2fL, 0xcf3cbad5d5c143a6L, 0x57b4042b9fcef2dcL, 0x2b55741691d9fe6fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x9f43289880e4f548L, 0x679ef8bfab27e68bL, 0x52ca2582269a8dd0L, 0xdb0381d56470907eL, 0x4cad2cff25d403caL, 0x48c210205801abc2L, 0x319698eee0a2757eL, 0xd2a47f7831e43f2cL, 0x9c07bae6d84a7438L, 0xed1d7921dff93d77L, 0x66a61815c3532e5L, 0x7b63e6d6b0bd85fbL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 100;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xdceb8db2b7eaba7L, 0xedfbe268d5b1fa6aL, 0xa78bfbaa13685278L, 0xfb9c2d0488c171aL, 0xd7d34194c3628c13L, 0x43b7716bcc143a46L, 0xefde7ae6a4449c96L, 0xbf9e80899ae2b710L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x82de615608c76a8bL, 0x9e0760f5e009de70L, 0x13dcc92f9c572952L, 0xce00bd446f820d48L, 0x47ec470393401b88L, 0x477a8089293b49a2L, 0x5c437d80ee42e88dL, 0x3e4356a607a49fe2L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x69051a44b059b1ccL, 0x91f893af0bc5b95aL, 0x1364981ee36e9611L, 0x80a042c0ba92622fL, 0xb2e23c9f3bf6f9b1L, 0x356f2630bbc25b41L, 0x3a05db80d5c0e088L, 0x34b4fe3476e47ad3L, 0x750fa87add48bee3L, 0xb00b7e8d0a57e405L, 0x6c50cd8588eed6daL, 0xbe46fa7426f5f62eL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 101;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xb9116811e6265857L, 0x883551c54058c4f0L, 0xf14601997e9349e3L, 0x9032299418429995L, 0x4b886945aa3399L, 0x3c4b7a5b3ef68b9cL, 0xab84ea6d3005205cL, 0x4f7cf2895cc20e58L, 0x3ffffffe3d8093c9L, 0xfffffffe7d8093c8L, 0x3d8093ca00000001L, 0x827f6c37c27f6c36L};
uint64_t A[8] = {0xe7f5ba6f2554f427L, 0xdf48518b3901ff96L, 0xa828c36c1d4e879bL, 0xef6c4ca1424432edL, 0xedc19f099a5676dfL, 0x8bf2891468410bffL, 0x27cf306a14944795L, 0xb6efb4cd4463768L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3f41888cd62e88e0L, 0x31668ab510bbeb58L, 0x35aeeebffd6ed52dL, 0xa39ccfcb004ef156L, 0x89237a023f37d63fL, 0xf0602a3cc0e00d7fL, 0x2aa91c179e457b82L, 0xefba2a817413082dL, 0x59c79387e970e739L, 0x6231eb02dd554769L, 0xf15c98f76253b79L, 0xeb1e5764ff5094dfL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 102;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x581b4711fdf2498L, 0x4a278686e1639607L, 0xaeaca9afd36b1afL, 0x64cfdc70d9453d29L, 0x435ac466954ffbb3L, 0xff6c1a78f9a2852fL, 0x20b021c3df219dc5L, 0x82290e253d61f6d2L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xadfeeb8858cee75fL, 0xb39892a238929f1eL, 0xd5a7b62826fe4135L, 0xf19b7e5353944d6aL, 0x7d6929a823d46fd1L, 0x821afc9c9cdfd923L, 0xb00c038dd1f7bbf8L, 0xa1625858237504b2L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xea8b63efa46a4712L, 0x1ec17c8433088f03L, 0x37ef6363f0b9364cL, 0x5d7d1fdbe64df580L, 0xf4658d92d9aacaadL, 0x7d64658d167fc51aL, 0xe38ecee4be9746eaL, 0x99ae2b200ee8e26fL, 0xa87d371738efc2c7L, 0x69710c1b572f0917L, 0xcabceb8d29c78f86L, 0x8ccba1e27a4f1041L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 103;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xbd427830aaad4bd7L, 0x195f0dcec28d3247L, 0x9181896bb258ecf3L, 0x421d124f57c0732dL, 0x3449b374e7e7b18fL, 0xc33a4b099ad0d596L, 0xcc31bbe49b99bd3L, 0xe54afb9740378d8dL, 0x50ffffffaeL, 0xffffffffffffffffL, 0xffffffaf00000000L, 0x51L};
uint64_t A[8] = {0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L, 0x0L};
// J nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xbd427830aaad4bd7L, 0x195f0dcec28d3247L, 0x9181896bb258ecf3L, 0x421d124f57c0732dL, 0x3449b374e7e7b18fL, 0xc33a4b099ad0d596L, 0xcc31bbe49b99bd3L, 0xe54afb9740378d8dL, 0x50ffffffaeL, 0xffffffffffffffffL, 0xffffffaf00000000L, 0x51L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 104;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe1abc2a39faa2be1L, 0x88f546e453a47562L, 0xa33370ff19188215L, 0xeb371270902f1c9cL, 0x2a5c42a1f4e09a44L, 0xa6180de78c61cfc6L, 0x55cd92e3a75bc83cL, 0x8cc423f9246b6700L, 0x8d2d930f72d26ceL, 0xffffffffffffffffL, 0xf72d26cf00000000L, 0x8d2d931L};
uint64_t A[8] = {0x793b80a73e500e39L, 0x3dc70d8c41726d51L, 0x327ba268cf29cc43L, 0x41754325b5ecc5aaL, 0xb9669b32568b37c8L, 0xbd6c661371ea683L, 0x73b527cb90a6ae1aL, 0xaa899fce49edefb5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xbad43565bdd6ac36L, 0x8db07fc9e2d252ccL, 0xb8d337f993974a4eL, 0xa5fb25c5a9ba958fL, 0x633766b12ccf5ecfL, 0xcdfe98874f8a7c41L, 0x1625426dc9e5773fL, 0x7130640a28fb1105L, 0x42d06d763d38887L, 0x2909c6b0f3d76b2eL, 0x6ffefa5accc3ea93L, 0x4bf8aa0e3ef8efc5L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 105;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf6b01fddbe143b2dL, 0xbb8465ed4fdb009eL, 0x838d84649b5c7978L, 0xc05f9fb7ded4c5d6L, 0x33bc1ba0e60395c5L, 0xea81a59184fa358bL, 0x5ac6be4767052241L, 0xbb2201ce71718e58L, 0x33d495ffc8993413L, 0xfffffffffc6dca13L, 0xc899341400000000L, 0x39235ec3766cbecL};
uint64_t A[8] = {0x47b8c90e0ec452b0L, 0x8691f46ed9af1fa9L, 0xda120f3433f2d27eL, 0x160837d249afa40L, 0xe0053424c4c03fc6L, 0xabd0d5874b2e52adL, 0xe28134da897595edL, 0xc9d2fe827d859fdcL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1825f2aafaf51b60L, 0xa308e73839a2c321L, 0x9ddfc12090798001L, 0x92b78db76707559bL, 0x592f1855f645075L, 0x6001e79ffdffd8a5L, 0x169fbb1ecf280b89L, 0x941b69d5a54870c5L, 0xccf88e8d75337bd8L, 0x55085ffbfa3cec33L, 0xd3a76a706000a13bL, 0x368e4264f0ea8634L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 106;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x87bb4fe2dc3244c5L, 0xea11b3af3bbc0d86L, 0x2adb0c558b5ae2ebL, 0x75b65b936f46b980L, 0x4065d35cb8b7f14L, 0x49e9f9abccad8c58L, 0x579ab34818287f28L, 0xa038b4226b120ad5L, 0x2583ffffda7bL, 0xffffffffffffffffL, 0xffffda7c00000000L, 0x2584L};
uint64_t A[8] = {0x5407a49b4faa0cf2L, 0x7eb23d3000f5ecf8L, 0xa2db87227dff4d2L, 0x6f0021dca8ee51c3L, 0x3e855bd6d766cb88L, 0xf50f8d1d5397f0dfL, 0xd0b1f024322e5746L, 0x3f859e44807206L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xf3b01e0f64bc3db9L, 0x4fbef3062444c7a9L, 0x87b060986f876132L, 0xd71417a19b0e590eL, 0xa564323c16577c24L, 0xc752e3ca44afd2d3L, 0xe6abe76c8be52d73L, 0xb86b8668afee8949L, 0x8bb0b0bf7291e910L, 0x5de24ba70cc0bd4eL, 0x38f38127533d94b9L, 0xa683514bb8949a68L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 107;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2745ee682fb8e477L, 0x557aa0f995deb12fL, 0xdfa1a3cf77c346b9L, 0x4158f80c85a37d1aL, 0xa669f71c5661865dL, 0x2ce99e65dbf40e1bL, 0x1cb16338209e6889L, 0x9f3a8add5f09020fL, 0xbe1bffff41e3fL, 0xffffffffffffffffL, 0xfff41e4000000000L, 0xbe1c0L};
uint64_t A[8] = {0xe22b104ad0f67420L, 0xbaf5500801638fa6L, 0xfe4601e2b5bf98aaL, 0xb2e97c5f8d1e0c72L, 0xa09a2ad2d0d67a2fL, 0xcf3cbad5d5c143a6L, 0x57b4042b9fcef2dcL, 0x2b55741691d9fe6fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa4d70907c301ae0eL, 0x1c2859b92a0a6c55L, 0x60301a6c7ee5ca1L, 0xd5c868bb7922ce5bL, 0x325253ea3380c6c7L, 0x58dd793c9a7421f9L, 0x2e4a97bdbd494919L, 0x926025d1387cee0dL, 0xaf95a5fe87adb9caL, 0x6e906a91b63d1c15L, 0x6212449fb5ebb030L, 0xf31d69a2a95bf18fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 108;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc9b029414eee11d7L, 0x4c02343eaefd62d8L, 0x9c0a908bd9a72ef9L, 0x15b349fb322ef9fL, 0x4b355c4104f6ef46L, 0x9243502cab9904bdL, 0xfe4b65513f282becL, 0x7be57cf09dd05826L, 0x797fffff867fffL, 0xffffffffffffffffL, 0xff86800000000000L, 0x798000L};
uint64_t A[8] = {0xbc2905fdc2c72f52L, 0x67f5f05fcd47bd28L, 0xc4a70bcc9535ceL, 0xea9479cf0f52d533L, 0x4ef0c2e2a7fb0657L, 0x5d1379f69267bcedL, 0xcc5ccf9a29159b0eL, 0x6febb404d5e365f5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x70f82cc0e789ab1cL, 0x11dc33e078d9be38L, 0x9b1a330ec2ecffe3L, 0x3df58109f7967fceL, 0x700c5cb1cae4fb39L, 0x32e6d1c1c01317ceL, 0x13f42e26e236cc5dL, 0xe303a0c6d181ec27L, 0x79e0052addd9ab69L, 0xc53d01ae5e9acc39L, 0x3b77ff922b24039dL, 0x8e222bdc4b6737c6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 109;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe0c12b2dbeed5c5bL, 0x8108260116b78d80L, 0x131596dc63f64aceL, 0x7fb1cfb3d4fdafbcL, 0xdfddff200ed201c0L, 0x932647f0da10de85L, 0xc7295a0d60dc45b8L, 0x135f7ac4a8fa30afL, 0xfffffffb655c0000L, 0xfffffffc655bfffcL, 0x655c000100000003L, 0x9aa400039aa3ffffL};
uint64_t A[8] = {0x5407a49b4faa0cf2L, 0x7eb23d3000f5ecf8L, 0xa2db87227dff4d2L, 0x6f0021dca8ee51c3L, 0x3e855bd6d766cb88L, 0xf50f8d1d5397f0dfL, 0xd0b1f024322e5746L, 0x3f859e44807206L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xc8e2daa96d7f9460L, 0xccf12c0ee6c63a3fL, 0xb75d25a661a975e3L, 0x63ec46f84f29f694L, 0xacea2fd6d6ef52ddL, 0x644c17168e404841L, 0xc0fbf0a1a0ce6369L, 0x332fa44864743f85L, 0xd93a1d82d58bcab4L, 0xcf68ff78d8730dbdL, 0x8edddf81c6819f3dL, 0x992eded4e7130034L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 110;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x18905f76a53755c6L, 0x79fb732b77622510L, 0x75ba95fc5fedb601L, 0x79e730d418a9143cL, 0x8571ff1825885d85L, 0xd2e88688dd21f325L, 0x8b4ab8e4ba19e45cL, 0xddf25357ce95560aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x34388d1781c06c9fL, 0x6bab4b917ad416d4L, 0x69e8676b0f741fb9L, 0x644183540e13bc56L, 0xc9e365086ce5a54dL, 0x25a1220971c2ab59L, 0x6b3a5852142b9a43L, 0xaa73fe0d6ef970d3L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xfdc4477ad9dc0544L, 0x275b2d188625411dL, 0xf157ef0baba4fe6fL, 0x67ba6eb282e190e9L, 0x92dc4322d5b45176L, 0x1027eeef72203c81L, 0x8d1046406b79aa82L, 0xc216cc89b0206582L, 0x1ba82da0dc8916d8L, 0xf1afd8660371f1c3L, 0xf42dd16eaf8669b7L, 0xea5a527ff56aa81aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 111;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x9f923fe2d79925afL, 0x1b12275f940da0c7L, 0xf875a7da5d23c27aL, 0x5a116150e224c725L, 0x6beb53017d64542L, 0x87efc838c1529768L, 0xfca8a670397d9890L, 0xfa6cb3747f36ffa4L, 0x270fffffd8eL, 0xffffffffffffffffL, 0xfffffd8f00000000L, 0x271L};
uint64_t A[8] = {0x316af5adbef1bf81L, 0x54fba1ffda268305L, 0xc880111a38792291L, 0xf2eb9417f1449b28L, 0x5238b7e0a70d7329L, 0xdca43f3c543f2e22L, 0x46c383c3194ad95L, 0x9b1496920dedc1cdL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x73ae5d645c58d9f8L, 0xde930cd98889c5e4L, 0xaaa1f25954742c1dL, 0x2f0de95e42862162L, 0x53dc80c5c8fdc0dfL, 0x1a0a47b9ca1d5322L, 0xdb3fc78d7fa035bfL, 0xcdd4d9c3656e7c5eL, 0xcdc07e2579066d44L, 0xc0f9590b2df0080cL, 0xb5f0cdf283b00189L, 0xf14bd41eb79b947eL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 112;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd50dc084defb805aL, 0x8f51dd4d85a781ffL, 0x4438773c13795527L, 0xc0bef4625d03851dL, 0xe7a3d2e4cbf97b91L, 0x206dfed75efccdbL, 0xadde3b37f6c350f6L, 0xd457da8369da4af8L, 0xcfdce7683023183fL, 0xffffffffffffffa8L, 0x3023184000000000L, 0x57cfdce7c0L};
uint64_t A[8] = {0x81d4d67d5303aa9L, 0x55d6984e2ed8d949L, 0x9ea7ce6365f0934aL, 0x69b60cd9343b297aL, 0xa916a98dc09558fbL, 0x4a43bfd951bdba86L, 0x6c7cc30329ddb815L, 0xd6b16ee90d413600L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x94040bdb95b1b956L, 0x35978e23f8c51c6eL, 0xb89fcb01a4b5175cL, 0x8ca69c916af16611L, 0x4cff2f5ef67a1e12L, 0x198914de0e6b9b32L, 0xca6ba2784a0c7adbL, 0xe70ef40d25d6a3cL, 0x82f6ed8284c87ddeL, 0xb398cc9ffdf8124cL, 0x857e2269c8f32bdL, 0xae7b7aa5bd2c87b9L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 113;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe0e95f6d008e5979L, 0xd3a597f3e4a1bc9eL, 0x78fde1043cc46f20L, 0x11974e8d4f084287L, 0x73147f1e375f2e2fL, 0x46281a77a6a25ae5L, 0xea832be5bd6141beL, 0x4ac12b4cb43fe513L, 0x2751afffd8ae4L, 0xffffffffffffffffL, 0xfffd8ae500000000L, 0x2751bL};
uint64_t A[8] = {0x63af8e6acb5e0ec6L, 0xf5834e0608329635L, 0x7d92074554ff619aL, 0xf9d2ee75a94e1debL, 0x50cb1436548daf85L, 0x7f722a578b70cebfL, 0xd6262937c36d4cebL, 0x639d60d651bee1e8L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x46d4d45aca25fa14L, 0x7341d394e10ad3e7L, 0x37422db35727a3e9L, 0x5f4809d837787d43L, 0x38c0ae759361ac81L, 0xf5744721ad0d711dL, 0xcc8040845e096f14L, 0x9675c939bf49ceb4L, 0x3057ccfc678b5d6cL, 0x8f0aa7a3e40d1d4eL, 0x28c183b0459bdbd1L, 0xde487805c86d2ed9L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 114;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xdcdf70add40ae53eL, 0x9c62eb9bffef44eL, 0xda55ce8722b7dad7L, 0xde1ca668cbf66dc9L, 0x61d0237c2546ec44L, 0xe484652185c64813L, 0x56a6d8962ed779f1L, 0xf4ee63dd47c90316L, 0x3cbfffffc33ffL, 0xffffffffffffffffL, 0xfffc340000000000L, 0x3cc00L};
uint64_t A[8] = {0x57fcaf64b5e8d6dbL, 0xf670e79ac97efbdcL, 0xe12253fbdb991b94L, 0xa928a6d84768c868L, 0x1d94d6153c3e2656L, 0x2085b6e8694a3819L, 0xea05005e197a2805L, 0x8004d784b244753L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x31b95a011bcf9bcbL, 0xc8d0a421668a0e73L, 0xdcddaa6646048fc1L, 0xa4ba89f329fcbc33L, 0xde648856b19f0f7fL, 0x42a8f77fcd1e91f3L, 0x8473c4a49baede0bL, 0x7d91cdc8cfb7524fL, 0xa6e3795ddef9bc23L, 0x35a72d5bfc9f56f1L, 0xb4264ac43a8d2073L, 0x9bf06e921743b854L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 115;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6529bb1744faf6c7L, 0x647710d5b2b71677L, 0xe17c94ff563f3ddfL, 0x1b8774b55993a6c0L, 0x9ada069be8bd049dL, 0x543c6b713a44afdL, 0x8062dc992f2f5526L, 0xe1fd560b6324cf26L, 0x797fffff867fffL, 0xffffffffffffffffL, 0xff86800000000000L, 0x798000L};
uint64_t A[8] = {0xbeab1712a6b7b41L, 0x4cf00f7286986417L, 0x7e5fa880503608e3L, 0xdfb258a6cecf99a0L, 0xb0bd6b72114b64bcL, 0x1ab4e30f608fb025L, 0x7ab0590d97c21cdcL, 0x7cca0f74c4dd4a53L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x14ab9015b5088bfaL, 0xaeb1a22536a03a67L, 0x33ca3366cb35e2a1L, 0xd3770ccae72a7713L, 0x9f1d128df469eb8eL, 0xcc72c89232b25622L, 0xf6bba894afaf5ec6L, 0x62bc3dfb566f039cL, 0x9530d0c41ca79eceL, 0xb7ab65aab0e502d8L, 0xce30ff6fbddc9f7fL, 0x30ce7a940a522439L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 116;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa3ba006a55f481aeL, 0xcf0b428e2cfdc4L, 0x2e317c0ed650d9feL, 0x697423792923a889L, 0x379bfd8e39294774L, 0x8ea11389be55b98fL, 0x1fd31b2c57a2da87L, 0x1d42004b66404980L, 0x17c37fffe83c7L, 0xffffffffffffffffL, 0xfffe83c800000000L, 0x17c38L};
uint64_t A[8] = {0x9327b0e9666b1242L, 0xf5f3ebfb4d392c57L, 0x7304174a87d08095L, 0x6869c3bcf7e94bb7L, 0xc3c5a8ebeeb43c51L, 0x3ce9943ebc307220L, 0x8fe1ecf0cfcb6406L, 0x710e6e6b5594a88L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1716f42b5d4a573eL, 0x3428d20980fa28efL, 0x45baba522cfed2ecL, 0x17f24d858b871502L, 0x25c4014d1145bcfcL, 0x812d06c08b1d22a6L, 0xabc2cf9370d9cc82L, 0xd1dc76f0337f85e7L, 0x5756b4f7facd2b0dL, 0xc3c1ebfccdc4ff8bL, 0x792d3623b0ebc408L, 0xe5e5d71952bc6f8L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 117;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xdf2a4e99987db828L, 0xd707aeea6fe330aL, 0xed8a6b41ba301cc8L, 0x53b2a120fcfe20e3L, 0xa75b19f0fe497fb2L, 0xb5b5fac1144295cL, 0x3b69af2ce9230027L, 0x47af04f55dca93b5L, 0x55ffffffa9L, 0xffffffffffffffffL, 0xffffffaa00000000L, 0x56L};
uint64_t A[8] = {0x63af8e6acb5e0ec6L, 0xf5834e0608329635L, 0x7d92074554ff619aL, 0xf9d2ee75a94e1debL, 0x50cb1436548daf85L, 0x7f722a578b70cebfL, 0xd6262937c36d4cebL, 0x639d60d651bee1e8L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1e2a9c61be1b01a3L, 0x51a204fe96f27a6bL, 0xc856b54e56edd300L, 0x2d31761544971c60L, 0x76a0ee761862d598L, 0x5cd1578fd8ec42fdL, 0x22f8ff7b9896bb36L, 0x72a9b0fc66de227L, 0xa9ee2c4f2cfba7b8L, 0x533f8ef39e231083L, 0xb0bd3ea0ea8c08caL, 0xe90923918352ba79L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 118;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xbb57e641a084ca8eL, 0x5d9528e035fb386aL, 0xc6c5dfb13f1234f0L, 0x3ed3b21fbb787ea0L, 0xa272c2520f433b5fL, 0x785d23260f1c41bfL, 0x1d9e322c34490dd3L, 0xcb0a2ba5679c519cL, 0xa4ff4f78390e0ffdL, 0xffffffffde0d5f76L, 0x390e0ffe00000000L, 0x21f2a089c6f1f002L};
uint64_t A[8] = {0xb79d949f7b27bbcbL, 0xaf2202c54f992674L, 0xd57c98ba98761d7fL, 0x2356181a763213c8L, 0x7007ce885822defbL, 0x3926281c4c80d90dL, 0x98b5c0d828160994L, 0xd2d05e64d4f0b73L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x285637c317004706L, 0xe9b19c5e28c09705L, 0xe1534e17bf4fdea1L, 0x1c8e7c32f4d21388L, 0xd81027bd70b99f47L, 0x1652a1a1d392382dL, 0x9a4ab02a72f49c36L, 0x5ee409ebbc7ba4c1L, 0xf70c825344967dc5L, 0x5bea517184de8f9bL, 0x679662741f37cda9L, 0xbdff09debe16cb58L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 119;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xfd6717db76f64df5L, 0xed29e18df77cab71L, 0xabbbb68402582479L, 0xb5ec2bdd5b613dc4L, 0x17096dd3687f13baL, 0x5b6d19eda2a78bffL, 0x1e3a1231b7a1bd93L, 0xba70d6773603de6dL, 0xfd0907b002da0ca7L, 0xffffffffffe31458L, 0x2da0ca800000000L, 0x1ceba7fd25f358L};
uint64_t A[8] = {0xe94a016c3e489b9aL, 0x4c0dcd300855ca85L, 0xed8e08d20eebc2e5L, 0xb358109f2f4b170aL, 0x4b5123a73a5b4568L, 0x581e5ff924197743L, 0x9860cd99345cdd47L, 0xb3ac042d1ac3e740L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa1804a77d3bf6a94L, 0x447d02533875977L, 0x32c5f6f4b703cb8aL, 0x4330a6530862d4d8L, 0xad119f4ae5a2f498L, 0x6b269d354fdcddc3L, 0xdaf83c60f3b4ba3eL, 0x4dbdfc91fa6301cdL, 0xc60008de7a788400L, 0xc014ef95debbe8cfL, 0xd364df1a3b2f8d82L, 0x3f1fd767e72578d7L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 120;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd216292cbc9c1651L, 0xac7a891087057dd1L, 0x5280082234ab10b1L, 0x498205e3867f0c4cL, 0x4dce25378dfeecfaL, 0x7fbfd0fffc2418c4L, 0x39c662bb67c204b2L, 0x907ad2d314f07741L, 0x5f06e5ffa0f883bcL, 0xffffffffffff69bcL, 0xa0f883bd00000000L, 0x96435f077c43L};
uint64_t A[8] = {0x3928c1c106f509cdL, 0x78606717982d7933L, 0xcd76320219721164L, 0x44a4548b2657625aL, 0x87fc58b7c9aa96acL, 0x4cd329009d86140cL, 0xaecf6bb41fcde04bL, 0xddf76dc6b51002f8L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xeb8ef5d57d54a6L, 0xd9d554eaf92e1755L, 0x45a67854641347cL, 0x600ad3763e53250eL, 0xfed5639ab1b532e9L, 0xf7c32358697e8e20L, 0x99b7b1b6db3fdc54L, 0xdbb71fb3c2384cb0L, 0x179fefdc067bf8b5L, 0xcba8dfe0bf9355c5L, 0xc1cda4924eec4f59L, 0x4749e803f300aac3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 121;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8764f0699d148ffdL, 0xed095a7728c0a63fL, 0x86bd67b50a9693a9L, 0x5b4bceb7322287a3L, 0x4f8535568876fa6aL, 0xc86be314cb98050eL, 0x9fd140759d8eca37L, 0x253c1d404d7d1714L, 0x9c80ffff637d6036L, 0xfffffffffffe6036L, 0x637d603700000000L, 0x19fc99c829fc9L};
uint64_t A[8] = {0x7306bbb8a15a8e04L, 0x8f02d66c01def11dL, 0xd63291c8154a67e9L, 0x7c6e85f3616f1ccfL, 0x1e787b17c6e02971L, 0xa4194c68b7b0ee5aL, 0x48bb709e959aa2bcL, 0xdc645794566e4359L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe1cc0f55cc666ce6L, 0x3e95832cb5ba1f1cL, 0x5b388eaa358d949fL, 0xee54570e6043c273L, 0x786737a27a39389cL, 0x52e5084dbb48af54L, 0x18d3c1b012f12d83L, 0xbfbb8785923103d1L, 0xb046d5a76b7db32fL, 0xcc6e239e5e857123L, 0xea5878f53c927868L, 0x3ed175c89848489bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 122;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4d13ad54d3ba5031L, 0x498be15dc423d8a5L, 0x7f18ec99da6c8d19L, 0xe6024ceadb766f65L, 0xf57223f8d8c75de1L, 0x2b6f92e1ea3f9972L, 0xb3ed630842c9540bL, 0x802cfb8bef253679L, 0xfffffffe6afd0700L, 0xffffffff6afd06ffL, 0x6afd070100000000L, 0x9502f9009502f8ffL};
uint64_t A[8] = {0x49b2a0b16a395853L, 0x32092e494617dd75L, 0xce614c2f83c516f2L, 0x40afd261d2a96d7dL, 0x735fd9b0767a558dL, 0x7c83d9d9520a759fL, 0xf34063ae496cce27L, 0x4270a2bd4b257a7aL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7eec0d6e52c60f2aL, 0xfb653b8584e1dcedL, 0x2f7fb1ee5fe58393L, 0xd1056459e47e49dbL, 0x93113f6e55fc1f84L, 0xefa86b4f47c2c0b3L, 0xe484e06cef685d6fL, 0xb63b2309399ed55aL, 0x722dd711cf7a8555L, 0x75213bb53ae48e81L, 0x8c0cfcb688a5c6c4L, 0x731296c38b5c2eb2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 123;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x85df439b0f91a396L, 0xae7d41db211d958cL, 0x46f1e1474b49f5ebL, 0x6863c809402f3dc6L, 0x87b56054c6e337f7L, 0x65458cf0a938f3e6L, 0xa93325fc5e1e4c8eL, 0x65bc689934f3e4e3L, 0x37ffffffc7L, 0xffffffffffffffffL, 0xffffffc800000000L, 0x38L};
uint64_t A[8] = {0xad8404a11b79aa6cL, 0x1d2617ed62ffc78L, 0x4eae27c831dccb8cL, 0xbe5e2550737095a2L, 0x4dc89bad3307af38L, 0xb1beed667e99fdc4L, 0xe114feaedd49af04L, 0xebaa1f3586a5d905L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x9af1a77eb0145446L, 0x2ae787ff735183bfL, 0x42db067e2ca13809L, 0xe72db9ba0e9c31d4L, 0x842f2a2e50cff16dL, 0xd7529214e94d9eb8L, 0x497e88c3ca18ae66L, 0x60c935ac50b30cabL, 0x7b92be8e9ecfd311L, 0x95db7a055811ac27L, 0x29af5d2b31455aa1L, 0x7229d351a6a4698aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 124;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6048fe2aa715573dL, 0xc31c471200e5e425L, 0x2ff45dfc31e2aa27L, 0x3820fec0a60b0402L, 0xd4f64a5344e3b4e0L, 0x30f5a09599f6afbbL, 0x3a5a2d952698743L, 0xf02304a8d6748fdeL, 0x2dfd3892d1fa7c83L, 0xfffffffffff7b516L, 0xd1fa7c8400000000L, 0x84ae92e05837cL};
uint64_t A[8] = {0xc69a65ed2bb2bb03L, 0xbcc7ceec7dbd337dL, 0x3743415af6fb167eL, 0xbc15743652dc1267L, 0xa739a6188ae5a09dL, 0xb4825fa5e5d035a7L, 0x44096ce747e2c679L, 0x97b96633aab52fc5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe006d27235855c0aL, 0x656831f36a98bb9fL, 0xdf7949aaac93a110L, 0xf5da0e35fad76244L, 0xad5ee1414e0828bcL, 0x57398c3f156f5e65L, 0xa7f95e5e22e899f4L, 0x5ef57d37dba4ee72L, 0x28096a009ebafa1eL, 0xc7f8b914c6790c02L, 0x74fae152407004b1L, 0xcc6a62cc31f17560L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 125;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8a054ee4a0fd4fdcL, 0xdfd652e57503df30L, 0xdcdf2cf6b4330202L, 0x446b1478939130b5L, 0x4b63a82cd006cad5L, 0x22d70d85d052767cL, 0xbeec377aca64f295L, 0x94334c0acd33d29fL, 0x34dc23efc7ab2e1L, 0xffffffffffc87520L, 0xfc7ab2e200000000L, 0x378adf03854d1eL};
uint64_t A[8] = {0x254a4a3e09ba48fdL, 0xf5f9a498bf1bfdeaL, 0x7c18faa630900f7eL, 0x113542810b0284cdL, 0xe97fbab46827f334L, 0x5b7d6c595db8b18eL, 0x669025d6306e5844L, 0xee79ebb98c19a4cbL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8cab4a122a5fae3L, 0xee6ba35c1ed62f7bL, 0x7a94c588520a2c18L, 0xdb7b556dee562cdaL, 0xbc7c6e7735b7bfdbL, 0xa5e8476b37360261L, 0xe2431fa62d28a98dL, 0x3033163d838ba521L, 0xdfbadd92348c4810L, 0x3e14ca552855990fL, 0x37969c7fd0221879L, 0x2468f3138bba43adL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 126;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xad725dd7e91225dcL, 0x7db9c09efdfc398bL, 0x600875e9b21032caL, 0x49221601dd7ddd1aL, 0xf03aa09ff36257b1L, 0x4493d1730970a09L, 0x8d677e6ca1bf0bdcL, 0x243ea0e757430233L, 0x6235f6ff9dca08L, 0xffffffffffffffffL, 0xff9dca0900000000L, 0x6235f7L};
uint64_t A[8] = {0x13b094a94e0de8bfL, 0xc1192e9bebd3fd5fL, 0x4426583cc2bc2fcL, 0xe3874e85b10c271L, 0x721a3a6c6b0185acL, 0x5bbf5051314aa975L, 0x8a3c17181c4402cdL, 0xe4a2b66f3663fbf4L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x2d792f81cc1900e9L, 0x2be7930fa2590df0L, 0x650cce3c2e335c24L, 0xdd67486a34a9a58dL, 0xaa10bd2f61448b02L, 0x8249c091ee3063b8L, 0x5d08d1d87a26b846L, 0x490e98f1410dc425L, 0xae7c0084a51341dfL, 0x15c9b31002cfe98bL, 0x1e878f201697fedcL, 0x893488c206aba848L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 127;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x1eabc1d7eccc4074L, 0xe0b3b306b8be9db5L, 0x99a3fcedbf0457d4L, 0x5aedc77a768c0774L, 0xb05806d060d0314aL, 0x69173caadb12f3e4L, 0xc147e7fa527cd6a7L, 0x86e2014c8cc77778L, 0x4528a140bad75ebeL, 0xffffffffffffffffL, 0xbad75ebf00000000L, 0x4528a141L};
uint64_t A[8] = {0x694ee4e9a8bd4f9dL, 0x77d335e552e3660cL, 0x523ce279ea653c2dL, 0xa16534739bad9f30L, 0x41c4e903744eda68L, 0x45a5457f2ba7c27fL, 0x578aa86076fcc7beL, 0x9a49e32de56a12e6L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x96b5d52b20042eceL, 0x43400dd67706b9f3L, 0xf7078ce133d56dceL, 0x55f6c761942c044cL, 0x84b52a04f00124c8L, 0xd9c774ea691dc9c8L, 0x1c90a81dec34ceb2L, 0x5fecbe76c3e5e6d8L, 0x39ac14caf6b18e57L, 0x8c94139e7a36c3fbL, 0x479dbdb7c3a8a03dL, 0x1c8defc6d3d0b252L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 128;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x699542c02205b526L, 0xa8c367a3e9e27836L, 0xd21a8b79ad7bbe4bL, 0x4813f697223f7706L, 0xdd9bc72ea1d490c1L, 0x2e6e25d723f3c4a6L, 0xd50bbd4780186240L, 0xed7891b504f33577L, 0xb964efff469b0L, 0xffffffffffffffffL, 0xfff469b100000000L, 0xb964fL};
uint64_t A[8] = {0x75b1deedf1dd81cdL, 0xcdedb3ab8dbc1d6aL, 0x6dbc4191c033ef74L, 0x99e398a2a8ab239eL, 0xd3e74166fb4fadeeL, 0x2bc2d83bc7d27b02L, 0xae7a6c8895365a36L, 0x163852f12b5f7327L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4a68d65450e607e8L, 0x77f0396799a95675L, 0xd1eb723528473a21L, 0x2abd0e4b2104aecL, 0xc173d4f54d07a8dL, 0x9e47941e180ec2a5L, 0x4c3cfae8ccfc9ccL, 0xfefd570672cf5c23L, 0xa86050c2e263817bL, 0xa97eea2b12deb97bL, 0xd91afb2ee278e002L, 0xe005684ebde7f697L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 129;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x619abcb9856aff78L, 0xf45f116f64ec7293L, 0xa14809aa7db8f7f5L, 0x8475d71a340b19eL, 0x2d60548fd075e0dL, 0x16f931f14a13e5b9L, 0x92abd9e41f4b1edbL, 0x6fa1886e95366e58L, 0x10229c36d370fe27L, 0xfffffffde3939a5eL, 0xd370fe2800000002L, 0x1c6c65a12c8f01d8L};
uint64_t A[8] = {0x480dbc1bdb128292L, 0xf4403cdc248a5658L, 0x326307428f89526L, 0x3daf9a43c81445f2L, 0x40613619d75d53bcL, 0xb13f2e85b503b962L, 0x725f5a062297d5b0L, 0xd4276cd13fed7f56L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xc2cbb24832f3915L, 0xed89af5b7c0992beL, 0x64acfec3f5ffdbbbL, 0x3b5c7fc5e4e32b17L, 0xded609d8d88d49b2L, 0xfa10aaf89b4acfacL, 0x6a4f4886a1efafa4L, 0x171c56fbdf47fb98L, 0x647a7cfc86daa09aL, 0xfb5d2bc97689b743L, 0x61315f16458af224L, 0xc45d067ceb4568e7L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 130;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd23700fe1a5e02e4L, 0xbfc6db91990aae4bL, 0xa73c6a728eb5fc5bL, 0x9c8e11d318feef0eL, 0x6d2cd9ead8a6c903L, 0xe29a07b96c38a67aL, 0x39def8be8cc0e058L, 0xed5bf9d21aae3ccL, 0x95eecfff6a112L, 0xffffffffffffffffL, 0xfff6a11300000000L, 0x95eedL};
uint64_t A[8] = {0xadfeeb8858cee75fL, 0xb39892a238929f1eL, 0xd5a7b62826fe4135L, 0xf19b7e5353944d6aL, 0x7d6929a823d46fd1L, 0x821afc9c9cdfd923L, 0xb00c038dd1f7bbf8L, 0xa1625858237504b2L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7ffc8b2821de9e8dL, 0x6de0af74e9d7b1b0L, 0x926d78f8b4abcd30L, 0x3f3d336f718e0fe3L, 0xd5a0893f584d7394L, 0x5203d9d6e505400bL, 0xbe7e6708ddc3721bL, 0x5b1f6f61af8b4c49L, 0xdbd3ae365db4c18aL, 0x8b7ea9db978143feL, 0x3d0c7b56aa95288fL, 0x58f543b80f29629bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 131;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4485df1cd35caa0bL, 0xc538f732b619a134L, 0xc66512c95d240fe1L, 0x621d4286c2ee5efcL, 0x79c42644e23f9492L, 0x92d0505a6987756bL, 0xac9e1ee44a6ddad3L, 0xeda1ed6e69ffa2f9L, 0x11ffffffedL, 0xffffffffffffffffL, 0xffffffee00000000L, 0x12L};
uint64_t A[8] = {0xb79d949f7b27bbcbL, 0xaf2202c54f992674L, 0xd57c98ba98761d7fL, 0x2356181a763213c8L, 0x7007ce885822defbL, 0x3926281c4c80d90dL, 0x98b5c0d828160994L, 0xd2d05e64d4f0b73L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xbea7c873ee0396ebL, 0xaf3cc02c20581721L, 0x713f0b17c44b0066L, 0x7e2e7e0fdc79130aL, 0xaf2691ab63655718L, 0x8303fd48f513e185L, 0x128ef6d72b3c11a8L, 0xf71485de49395c4dL, 0x2c783178c4aa3307L, 0xe0cdbd6c8b26bfe9L, 0x8b5bf866b646da84L, 0x1b466d5af01006daL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 132;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe05b3080f0c4e16bL, 0x2cc09c0444c8eb00L, 0xabe6bfed59a7a841L, 0x75c96e8f264e20e8L, 0x86659cdfd835f9bL, 0x2b6e019a88b12f1aL, 0x56af7bedce5d45e3L, 0x1eb7777aa45f3314L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xe94a016c3e489b9aL, 0x4c0dcd300855ca85L, 0xed8e08d20eebc2e5L, 0xb358109f2f4b170aL, 0x4b5123a73a5b4568L, 0x581e5ff924197743L, 0x9860cd99345cdd47L, 0xb3ac042d1ac3e740L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x19b2a67a3ce970f5L, 0x14774ce11f6a6617L, 0x752421ee03d61f15L, 0xd0cb7d9857b7ae3aL, 0x1eaaa222d4e37f76L, 0x69f0bc821080c4cL, 0xbc2d7fd4e51bff6fL, 0x4f83d3b99660a000L, 0x8eed0eb4d83ba2fL, 0x1f4d312bc38cdf85L, 0x41a748e4b5441aa4L, 0x3d8ea21008fcf622L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 133;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x9027be1378bab499L, 0xbfdca21d08c7df97L, 0x7ffdbe1cb29888d8L, 0x334aaabfe2233009L, 0x2295b92c55f98aeaL, 0xe0622b4677cdff9fL, 0x16696f94bc41383bL, 0xd006e604c743e5ddL, 0xcf7e8dff308171fbL, 0xfffffffffffffffbL, 0x308171fc00000000L, 0x4cf7e8e04L};
uint64_t A[8] = {0x76548399d85ace5fL, 0x70a82d4017a5e8e3L, 0x76ee5bb938b24a69L, 0x7b3d5bcaebcf2c1aL, 0x6e1b7c097bae3101L, 0x28fab9cb4527dedL, 0x1395eca430a44026L, 0xffa0b8e0cfa7cddaL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb43a151803634d77L, 0x4cf46a28d8072fcL, 0x15659b4be34521bdL, 0x12cf1ec3af915effL, 0xf6a81f388096bceaL, 0x877afbea92e9b5e7L, 0x5b9dd55ce1858cd3L, 0x744211ea959e4443L, 0x9034786e5b1a8e37L, 0x50c1e66e1cfc8257L, 0xd4ffec06adf2c92aL, 0x976a37d530cb9f73L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 134;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4b969974eba78bfdL, 0x6b20afec715af2c7L, 0xa624fa936c83906L, 0x283c7513caa76097L, 0x9bbff86e6dddfd27L, 0x4819d515ded93d4L, 0x9b944e107baeca13L, 0x220755ccd921d60eL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x1194785fc0ebd864L, 0xae08dba305d1c30L, 0x637a496883bf13e0L, 0x1e59d7ad07931b9L, 0xfe138e7c3a8da79fL, 0xfaa2ea66baccab45L, 0x46610f593244345L, 0x990198536bb2cc87L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x268984e8bfbdb45eL, 0xb68de9a874012eafL, 0x216a5d194f9708a9L, 0x7030a56ed4e5ec1aL, 0x13df7a68009254a7L, 0x744febdcb99e2e76L, 0x27810f9a51fe9523L, 0xd1a6892ad65d48c8L, 0xc5fddee9d5444c67L, 0x9fbfddcdbf022969L, 0x5917f9c04cf6dad9L, 0xd9a9286705d1d121L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 135;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x3a707e90687d1b06L, 0x93c65a752a208afcL, 0x94789a0863d56ca7L, 0x5afd12a37d56dbd6L, 0x7372b23b09de2d51L, 0x8ccfb2f077954588L, 0x8222adbc119bb6bbL, 0x9fbd4e9fcbf7d9f1L, 0x19a0ffffe65efffL, 0xffffffffffffffffL, 0xfe65f00000000000L, 0x19a1000L};
uint64_t A[8] = {0x1ac9b3b95c98837aL, 0x8d80cea9a6380e97L, 0x68b05abd2b4c70a9L, 0x1297113175774cf6L, 0xf9b38f9d5ef51755L, 0x5566e3f4088317ddL, 0x279b1cdeee4dfc85L, 0x58aecf8f412543b5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xbc1343775d00a2daL, 0x9148c4dea8f74874L, 0xc88dfe936b40bcc0L, 0x3d59a9d214daae5cL, 0x66b307ce9b83fb26L, 0x4f9c4ad381918361L, 0x47887cb08cae9b50L, 0xa7bf7f6deb2f1becL, 0xac99b6626bc74118L, 0x818fbb41e8725333L, 0xd47799c152c51d1bL, 0xae9e298f0f854d53L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 136;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd4b3f7d687f0eea3L, 0x6eb032cd013c6b44L, 0xc14002ace0c52973L, 0xedc51f7a7005077aL, 0x4884fe5c88123f77L, 0x2bdeb38e95fa9aacL, 0xcdaa3e08ed62b802L, 0x7f85b0e3b519a7bbL, 0x16c7ffffe937L, 0xffffffffffffffffL, 0xffffe93800000000L, 0x16c8L};
uint64_t A[8] = {0x1b8e99ec73674fd0L, 0xdd2db1ac1c655c22L, 0x6961af51e2d8306bL, 0x8be27de7f56e210fL, 0xfb1256c27d874a2eL, 0x16f5d1e9cfdaa431L, 0x8fc19cbb4701173dL, 0xfbfe9539b70e2b92L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xed20310fb0957f05L, 0xe223d35bebc3efa9L, 0x649105bd059f08d7L, 0xbb4d31d046b12ca6L, 0xfc58157cd121bba8L, 0xf6e31f4adad95755L, 0xdf57065aa10c7c59L, 0x9811a1cb42769404L, 0x3fbce9e8baa4d711L, 0xbd97c97d239858a2L, 0x576bc96e0faec5a6L, 0xe1c0ee19f9f8b72eL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 137;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa0a7e915778804fbL, 0x9e406c8ab737892bL, 0x7f39ea79842d63adL, 0xa599b6cdb16d03c5L, 0xa4d38b8fdb4cbcf6L, 0x5331a0f8643d13c8L, 0x84bf095410b3726dL, 0x7f5703b730df8657L, 0x24c0ffffdb3eL, 0xffffffffffffffffL, 0xffffdb3f00000000L, 0x24c1L};
uint64_t A[8] = {0xad8404a11b79aa6cL, 0x1d2617ed62ffc78L, 0x4eae27c831dccb8cL, 0xbe5e2550737095a2L, 0x4dc89bad3307af38L, 0xb1beed667e99fdc4L, 0xe114feaedd49af04L, 0xebaa1f3586a5d905L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8c2d9bca9e660e3bL, 0x153c12709c511bd3L, 0x6dc74c5d56d266f6L, 0xa4344fbe7ea3becaL, 0x5491488889769c6eL, 0x3fa8733855f49f0fL, 0x9131fe15e087833cL, 0xbd0d21fa112d18e8L, 0xa12a1840970f9452L, 0xa1d2cb56a4fa9cf2L, 0xedc4406f84de5e9fL, 0xac3cf5715f483262L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 138;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x469f7b9e0ec598ceL, 0xcbef2055f11abbaeL, 0xf500ec13afd839cfL, 0xba48cdf9ab862f82L, 0xdcb4e18ce5653d9cL, 0xa6990ee87d3d6a43L, 0x8485ce46cb29c1fbL, 0xda1a168f7154d61fL, 0x75e1357f8a1ec302L, 0xfffffffffffff882L, 0x8a1ec30300000000L, 0x77d75e13cfdL};
uint64_t A[8] = {0x80a698c8975ead83L, 0x90db4fbacc824d66L, 0xe3c23575a8e79d32L, 0xe8f79d0c8916774eL, 0xc07e51672184d151L, 0x5c15e89541c00f8dL, 0x49fa74271f568f63L, 0xf0d5282b6039e3a0L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8a0e172e1bd6030cL, 0x1f3cb532f04f5e91L, 0x4da1bf6c06eb61daL, 0xb5d022d2e972d2e4L, 0x9bdd085aa4a0d73aL, 0x5868d18b82247c04L, 0xe2079f99b7da0ec9L, 0xb5d5e549fa0ba494L, 0xc0ab1f7adf6d1a2eL, 0x3e18bdf96ec45cbaL, 0xc511df517776d730L, 0x8b53a7aaac498a35L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 139;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x63cbc81edab3c39dL, 0xfc68133ee6391fb0L, 0x76edc081aab5f779L, 0x620db96ae4901c68L, 0x2465824d63cd3c97L, 0x1eebe65f0f223d17L, 0xd2ece0b4e96f06ddL, 0x31cc7cfaa0b838efL, 0x8fffffff6ffL, 0xffffffffffffffffL, 0xfffff70000000000L, 0x900L};
uint64_t A[8] = {0xc7ddf7864ac64482L, 0x80cb53c4c9ac79e0L, 0xb47cc1f1216cd550L, 0x1df4d36fc0aec63fL, 0x7c792a6f445611f5L, 0x7002065a567a0793L, 0x817c6261de6732b9L, 0x753e20a3ae511746L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xd29ffba5252b6077L, 0xed88c0ee776a31d4L, 0x46d457aade6a3a1cL, 0x71d8769a0adbb240L, 0x67b4a8fcd8fde65eL, 0x582e4926b64f8763L, 0xc4839fdc923e01d4L, 0x6d9ffe5a94750d61L, 0x7a0c95c215bb614eL, 0xb99ef0f8dfda1017L, 0x13434a13bf9ae9a6L, 0xc02cf0828f276a5dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 140;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe94f7d346d823278L, 0x1b1e8ae057477f58L, 0x32940b946c6e18L, 0x1ee426ccd5cd79bfL, 0xd73acbfe2cd9e6b5L, 0x772ef6dec7f80c81L, 0xc5254469f72b33a5L, 0xc747cb96782ba21aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x47b8c90e0ec452b0L, 0x8691f46ed9af1fa9L, 0xda120f3433f2d27eL, 0x160837d249afa40L, 0xe0053424c4c03fc6L, 0xabd0d5874b2e52adL, 0xe28134da897595edL, 0xc9d2fe827d859fdcL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x55ac55abd2066b78L, 0x5c4b4035e72e2204L, 0x16b59961e5283d57L, 0xdc3d35e982735eb5L, 0x4743897245424087L, 0xf1ce02509e7130caL, 0xf34a8ff5a99dd3eeL, 0x37d192e2abd6777eL, 0x5e694bd8a1422039L, 0x6b73698e8267a051L, 0xd9df7b299f866465L, 0xe27c5cb04ecd8080L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 141;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x985cea6fc03dacbbL, 0x98d44e502ee3897eL, 0x3947e7d055d2b50L, 0x7a9c3580299c0b1bL, 0xed778c1f13b3dcdbL, 0x5189aacaa7114b7fL, 0xacc151e98a31a32aL, 0xb6144842f71699eeL, 0x3a2f7fffc5d07L, 0xffffffffffffffffL, 0xfffc5d0800000000L, 0x3a2f8L};
uint64_t A[8] = {0x6efa6bd995c6f13dL, 0x7569e3ebece891e4L, 0x5397ae9b8df4ab71L, 0xa57863aabb662998L, 0x9962f967bbe4fb12L, 0x26a08b12b08fe94dL, 0x8d9fe2a2db5bf5feL, 0x901a055991b40621L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa4a3fab8d03448acL, 0xece0c7e33ae29b09L, 0xf977b67900d74515L, 0x6c1778aa2b6ac6bfL, 0x1ac99c7abb407b7L, 0xdb82b225331b1c18L, 0x9a5029be88bb695L, 0xc0bc388e7a476ab0L, 0x3089904606e34f07L, 0x91b2ac06fe699eeL, 0xe879795838adbc88L, 0x10f4d50c81edeb7cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 142;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x624402d9ee328356L, 0xe241d8c53368010eL, 0x1df145170f4af4f4L, 0x1535126d48f0d2afL, 0x51ad7fed5427ce4cL, 0x4cee44686a65700dL, 0x6ced5c6441a052c6L, 0x8ee577a9c289b3b0L, 0x2dace9d8d25312aeL, 0xfffffffffffffc87L, 0xd25312af00000000L, 0x3782daced51L};
uint64_t A[8] = {0x9b1d73d30c074c77L, 0x7066b28e4e81f4aaL, 0xc693f6041e7a86d1L, 0x571b9ffe1b1ce20fL, 0x146428ccc2a6d239L, 0xe739711ae0613c3eL, 0xcac27df8a27cf75fL, 0x4f08c45d910349ceL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8920fa356c134d95L, 0x3ce8abe88f27b6caL, 0xdf74fb720fa00667L, 0xe56aae507c0deaa5L, 0x98a7596758cd42cdL, 0xed78d55caba83d6fL, 0x90dd05039f26c851L, 0x5666cc70d0e37f68L, 0x6befa62174fea206L, 0x1165029e17febcfcL, 0xbfc2a7705afd2640L, 0xb660ae88fe79857dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 143;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2abcae5bd8d312f5L, 0x48e1c4580b462b1cL, 0xe08c0ca5ea11770dL, 0xc8b6758df6b6cbddL, 0xe7ef5a7b0f0b3c49L, 0xf9b58178221b8e99L, 0xbf2f3b74a57bf57L, 0xc1b6e3fb22ff2505L, 0x1affffffe4L, 0xffffffffffffffffL, 0xffffffe500000000L, 0x1bL};
uint64_t A[8] = {0xbdc3f5804558c906L, 0xbe50b32eac05abe5L, 0xabf8eec667de9f04L, 0x30c099e05035eac8L, 0xc2a65a2b6251ee57L, 0xaa1010f7e96e7986L, 0x9f80c4fdf2efb104L, 0x22e94574db40cdfaL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3ec038ece9989df8L, 0x6d4a1d4f8fad738fL, 0x1526c718b986a4a3L, 0xdae74f7ada9b04b9L, 0x740feecee6c326d6L, 0x23345dea82c51219L, 0x9e0c711bb1f023bfL, 0x86ec1a91a268a1d9L, 0xefbe9a9cfb2508a3L, 0x6f1082b07a90fa9L, 0xb5d9124b81c4b0bcL, 0x3d38a3be1c3b4802L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 144;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf6a0d541eeaf94c4L, 0x98ede67e35d60e4dL, 0xf6854c21d49f0e81L, 0xab6cf59c8d51c084L, 0x6a3092dd2e588f90L, 0xf98675a877100653L, 0xa3a37c8485b85ed6L, 0xf3f37d646dbc52abL, 0x16c7ffffe937L, 0xffffffffffffffffL, 0xffffe93800000000L, 0x16c8L};
uint64_t A[8] = {0xf00d7f44b2f20021L, 0xfe99579267f76431L, 0xb1a0fe6b4bfe1d41L, 0xe195a18004d3be6aL, 0x571d7288cff1ca50L, 0x9919dc11de5299d0L, 0x7e613e6125db8f74L, 0x831ba6a0cd03d645L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x99e7bb5d06b8906aL, 0xbeea1f619d5bd816L, 0xa9edac5239bee892L, 0x7ec23d367ef05c6aL, 0x28309036df24c0a2L, 0xfac7fdc3ed0f09bfL, 0xe3b5e2820c28319cL, 0xef04e156af132d39L, 0x2cb0cdc4274e4a96L, 0xb942cf3efbd25469L, 0x9aa821f7a93a8c24L, 0xddcf679962e26281L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 145;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xbd88aca74765b805L, 0x3ea123446310eb5aL, 0x62d51e29fd54487dL, 0xc1ee6264a7eabe67L, 0x7150f87e7211e445L, 0x7ab49dd209f98f9aL, 0x640388f83b9fffefL, 0xb7b284be14fb691aL, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0xc9a5bd13954b9ca2L, 0x566feeb4d61328caL, 0xcfd7bf48e54e1acdL, 0xeb2603b57b7acd4dL, 0x7bcdd0ff094f23f1L, 0xcb8721ecb3ec12b9L, 0x9e4cbd67c300f661L, 0x31ccefd32ba4dc4cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa0228e62b65386c6L, 0x5e8c3b095e2b5d7eL, 0x205b27c6cd16150aL, 0x4220d2b7676a4604L, 0x5482d87c8da6eaeaL, 0x99158f0d6038e7a8L, 0x46a5ff4ea6ec67f8L, 0x444f7637ef0ced1cL, 0xc1d106c4de5e49dL, 0x17cecb7073023d70L, 0x6d02a11ee7f9d250L, 0x2937a150d3900ee6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 146;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x85f708f13daeb8acL, 0xcabba876e7b85261L, 0x3e1f0fe041c49f28L, 0x5435fc73e47833f4L, 0x5cd3f846da3f0ecL, 0x86a81d067c1d17e1L, 0xbc84758af496f4aeL, 0xbe44742c39635213L, 0x8baa277f74559d85L, 0xffffffffffffc505L, 0x74559d8600000000L, 0x3afa8baa627aL};
uint64_t A[8] = {0xbc2905fdc2c72f52L, 0x67f5f05fcd47bd28L, 0xc4a70bcc9535ceL, 0xea9479cf0f52d533L, 0x4ef0c2e2a7fb0657L, 0x5d1379f69267bcedL, 0xcc5ccf9a29159b0eL, 0x6febb404d5e365f5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xac3700988354633aL, 0xf8b90e4c5f38b059L, 0x81849adc894f66a3L, 0x4f05ab1a873636aeL, 0xb0311444694be885L, 0x8349f222a63c27deL, 0xdd206251c15d175L, 0x4f6c680ba18e80a3L, 0xdcaa046e4fddea6fL, 0x69e611d2bcbc8deaL, 0xcd897fe037ac3d39L, 0x989c2d128c60addL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 147;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd61a0fd503baab7eL, 0x82f620d3e6d45796L, 0x4b4284f5457f960eL, 0x786e91c5322dd81fL, 0x843389170ad09c87L, 0xd0f611c4511ad2dL, 0x1e94c7fb18c4e74fL, 0xec0b74af155f0fe3L, 0x816401c07e8e01f0L, 0xfffffffffff203b1L, 0x7e8e01f100000000L, 0xdfc4e8171fe0fL};
uint64_t A[8] = {0xa5e6364e9e77bbcfL, 0xf24e320e9d2f7afdL, 0xb3ffad5da080cb89L, 0xa5b920c9addbe7d6L, 0xa48bc48eff5305b4L, 0x1e9ec8dc1f4abc99L, 0x83bed21da1311a81L, 0x6c5b6c794410eb82L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x569800f0ff446553L, 0x2580442cf1250ec3L, 0x65be6d30fe41477dL, 0x9394fb4a5717091L, 0xb848776cead0f082L, 0x3ef41393915b2a7L, 0x1a16f1d40e05fbb8L, 0xb7724725094cf56bL, 0x7540056588b6cec8L, 0xbd474f4592c0bcadL, 0x26c9415b17621de4L, 0x59ca25e4099b958dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 148;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x650a582f60fecea9L, 0x615d44267ed012a7L, 0x257ab863ef51467dL, 0xd4126b96b7366529L, 0x28e8eb3e69242fb5L, 0x4c59598efbf5cd12L, 0xeacae38bbaa69cf1L, 0xcedbc503e9f4ba61L, 0x1d8ab1bee2754aabL, 0xfffffffffffffc6aL, 0xe2754aac00000000L, 0x3951d8ab554L};
uint64_t A[8] = {0x46ed86f948a08edcL, 0x3f5b4c65383e91dfL, 0x8f4f9ba66ae7ead8L, 0xca5477de61ea9046L, 0xa091153d7642156fL, 0xc433ce04b59fca93L, 0x3b33c627d44fcef4L, 0x51c35033d6d90800L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x26da27b725e7d90dL, 0x6d8ea5a1b49c6267L, 0xea7c2149a7c6cc0bL, 0x1844d55f47b432b5L, 0x35afff20a4ed884cL, 0x8efe40016cce46f7L, 0x54d1fbe983b712ecL, 0x225bf513d24cbe83L, 0x3852aeb36bfb8226L, 0x79a43a09f2e813caL, 0x9a08dd59dd7a3460L, 0xf9e129deda72799cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 149;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x19ad0bc3e23150f9L, 0x5a8088f5a828fefbL, 0x46e82b2919b15c00L, 0x9be15868bdba1ebbL, 0xee9da0bdd485b903L, 0x83d6e3b02348b73fL, 0xa797386711143a36L, 0x9e78855bf38afac8L, 0x6f300e9290cfef29L, 0xfffffffffffffdbcL, 0x90cfef2a00000000L, 0x2436f3010d6L};
uint64_t A[8] = {0xc7ddf7864ac64482L, 0x80cb53c4c9ac79e0L, 0xb47cc1f1216cd550L, 0x1df4d36fc0aec63fL, 0x7c792a6f445611f5L, 0x7002065a567a0793L, 0x817c6261de6732b9L, 0x753e20a3ae511746L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa83339fca8b4c2eL, 0xb9d7a1537c257aa4L, 0x84687ad3964f6614L, 0xe545867dc39f2bd9L, 0x27777101e0cc9dffL, 0x3eff4e8c632aa516L, 0xeb20f41ad71a8fc7L, 0x40ac8e528a8b25a1L, 0x12469fcf2a4c0e94L, 0x88b95f1de7d1a7dL, 0xf8770e002986a66fL, 0x1d5bed367ed0ae2bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 150;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xfd34ec9f7a5cda19L, 0x414895d0fbbad412L, 0x7c1b7c24c12ebfd1L, 0xaae0296848c3f3afL, 0xc57934e5a5ebe688L, 0x6bf544af1164eed9L, 0x138f6551b8e0a725L, 0x3f4f06a02445489fL, 0x222bffffddd3fffL, 0xffffffffffffffffL, 0xfddd400000000000L, 0x222c000L};
uint64_t A[8] = {0xb7b80a3b92f33f24L, 0xebb8c6eda66109f4L, 0x3d4e414d5ae125d0L, 0xfe4bac5d667b36a5L, 0xf91df8af155ce79cL, 0x36c0fc867a2482aaL, 0xc67961734171152fL, 0x7ed40f8766c8520dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x77276921445834f8L, 0xce9c16e913852d75L, 0x44a29232e6c7d188L, 0xced1a746d1b3a8dbL, 0xd9da69122e23c2aaL, 0xacf96f2cdd3c1db1L, 0x83accf95eb8e6a3bL, 0x15f7bf17364bb3b1L, 0xbd1d31a56698ebb4L, 0x2d3b4afedaa0f643L, 0x979193bedeab8547L, 0xa929afded1cc6900L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 151;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x354162a229432a5fL, 0x27982f66a7ee78c1L, 0x64248557d660cf90L, 0x4dc586d6d36d0e32L, 0xacac2b6a9f4f3e54L, 0x97c59e9a93f6d175L, 0x80df11498db65a3L, 0xeb73dc2009e4fab6L, 0x6f90ffff906efL, 0xffffffffffffffffL, 0xfff906f000000000L, 0x6f910L};
uint64_t A[8] = {0x254a4a3e09ba48fdL, 0xf5f9a498bf1bfdeaL, 0x7c18faa630900f7eL, 0x113542810b0284cdL, 0xe97fbab46827f334L, 0x5b7d6c595db8b18eL, 0x669025d6306e5844L, 0xee79ebb98c19a4cbL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x48daefd26ad99a6bL, 0xba1d1dd4685c55b1L, 0x75eb554dda5c705aL, 0x1add601104951c2eL, 0xb164592ec0a5cf6eL, 0x842cbf9ef4edc7f5L, 0xfe01e3401347dba3L, 0xa7c11bc5a35fe7afL, 0x6dedd67597030865L, 0x8f519be549923909L, 0xbb6f3e44e1b12778L, 0x78cbd0be8661731cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 152;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa5c68ac7c49da1ddL, 0xedc9fdfe17692190L, 0x797bd4feba7b6aa1L, 0x6e52ecc4b5867b11L, 0xd7b680b3b127a920L, 0x8ff72140e1d8fa24L, 0x6d51665c1811b30bL, 0x1896e2537be95c49L, 0x22ffffffdcL, 0xffffffffffffffffL, 0xffffffdd00000000L, 0x23L};
uint64_t A[8] = {0x80a698c8975ead83L, 0x90db4fbacc824d66L, 0xe3c23575a8e79d32L, 0xe8f79d0c8916774eL, 0xc07e51672184d151L, 0x5c15e89541c00f8dL, 0x49fa74271f568f63L, 0xf0d5282b6039e3a0L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x987fc2d925e4d77cL, 0x5af45a88d8d3ab4eL, 0x5d1e849e0fd0e0e0L, 0xf05e55d49873cee6L, 0x5a88e783cc05a63dL, 0x2c55fbfbd1f026faL, 0xdbe0b12a62aa3c9eL, 0x7b2f2d0aab1848d2L, 0xd3919de29c20bc4bL, 0x27c4706c0fb9b842L, 0x8340fdd0bff5295dL, 0x6115438eb43cb53aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 153;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4df5b860297fb25dL, 0x21e265a503e6c90cL, 0x4b208816ae9209a8L, 0x7f656262b379dc98L, 0xe0117e7fa0f2f4f6L, 0x8a951cf34678363eL, 0x19629b0595378b3bL, 0xb2f71f2f09c59664L, 0xcb0fffff34eL, 0xffffffffffffffffL, 0xfffff34f00000000L, 0xcb1L};
uint64_t A[8] = {0x9aa4819ec5eb4a3L, 0x843d527627103033L, 0x4fb6be2872eb797bL, 0x63408a083be2d806L, 0x2df5acb69dffcb33L, 0x7a7d39ea8034a362L, 0x63895b730257c52dL, 0x6f93d9ef8f89e6bbL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb9fbbdf93263d0d9L, 0x76d971e544994053L, 0x9b14e10cd4bede06L, 0x6ab770db44c439f8L, 0xf404cd19a6092517L, 0x5e73b49ccfe6e389L, 0x47c7b996dc16b9c2L, 0xd9f7957ccc9f69ddL, 0x1365e0e74438a0e5L, 0x5e609101cc69cb51L, 0xf7181e73927a9ca5L, 0x28a4614debdb0029L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 154;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x430d5e4ab5df3c9bL, 0x8c670f48afd80ef7L, 0xd42a5d33e8bd2eacL, 0x75932b5a0ce3648fL, 0x85e8cb92559f6e61L, 0x1ccfe774a318b0c6L, 0x34795a2233dec6d7L, 0x7d1b46703772f037L, 0xb22552024dda664eL, 0xffffffffffffb851L, 0x4dda664f00000000L, 0x47aeb22599b1L};
uint64_t A[8] = {0x6efa6bd995c6f13dL, 0x7569e3ebece891e4L, 0x5397ae9b8df4ab71L, 0xa57863aabb662998L, 0x9962f967bbe4fb12L, 0x26a08b12b08fe94dL, 0x8d9fe2a2db5bf5feL, 0x901a055991b40621L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7bbecd8f39f6c882L, 0xd43c4f01561d5320L, 0x33bd5f239a08f73bL, 0xc6bf940a9514747eL, 0x90972797fe1a9ec7L, 0x24f68dba10266af8L, 0x17b017785c90023aL, 0xb580ae449aea5911L, 0xcec47528ffe48660L, 0xa55644ee23c91f31L, 0x97a0a83739a5cd13L, 0x83d3422ea8cedac8L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 155;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xbdd7be73ff3b0e26L, 0x483a800830026014L, 0xa0dd0f20cd3abdbeL, 0x608fb93c1344f04aL, 0xd5ee8291abda75bcL, 0xaf68241cc7940688L, 0x188b62a5f177006dL, 0x4ff03bf21c599f3aL, 0xfffffffefffffc00L, 0xfffffffffffffbffL, 0xfffffc0100000000L, 0x400000003ffL};
uint64_t A[8] = {0xd0b0671131fd2990L, 0xc1ae39aec57d9af5L, 0xec4f42848208877fL, 0x8aa294eae8afb3c0L, 0x41079060e7d3e5b8L, 0x4b6bf603533d6592L, 0x995c19d2027b16b1L, 0x42451d855831a204L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x83d80ce0e75ed204L, 0x213bc6a96f70dfbcL, 0xc8d379b4496cb08L, 0x3fbf50f8415a112dL, 0xe34e4c8a3b34a89eL, 0xfbe135e5a90ac3c0L, 0x46d923d92baddcbeL, 0x9745f65fb955fac1L, 0x60956a17b3b0deebL, 0x587cee8ec90493e2L, 0xfa9017d241c673dbL, 0x6929add84ea50870L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 156;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd704063841af3718L, 0x17451a4855ae0abdL, 0x6ba362cd8f942b7L, 0xf622bbe99af3e008L, 0xb760abbaaa20028bL, 0x5e16fcab8c57f2bL, 0x3c269d18e489d51fL, 0xcb011859d5a577c2L, 0x62ee7fff9d117L, 0xffffffffffffffffL, 0xfff9d11800000000L, 0x62ee8L};
uint64_t A[8] = {0x47b8c90e0ec452b0L, 0x8691f46ed9af1fa9L, 0xda120f3433f2d27eL, 0x160837d249afa40L, 0xe0053424c4c03fc6L, 0xabd0d5874b2e52adL, 0xe28134da897595edL, 0xc9d2fe827d859fdcL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8b173cda79c56159L, 0x783f2c4d8b24adc7L, 0x13ee9a90dd09509aL, 0xd5e5e4d9bf828cedL, 0xfa8901e477a15e2dL, 0x91e695c255b17872L, 0x3ab9deadad1de3bL, 0x79067e497ae74094L, 0x3864e708bb04e63fL, 0x9dc461692d0c3961L, 0x65ea2460be9edb44L, 0xa2091c9f7c5759bcL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 157;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x140d71d599c6d82bL, 0x5a0a0d39221c2aecL, 0x8d76ad4dc584b883L, 0x1e2319958183997bL, 0x3649592ae59617dbL, 0xd282794361c65305L, 0xd80809f453141b07L, 0x95a6c20d067df35dL, 0x6d1c23889212b511L, 0xffffffffff2ed89aL, 0x9212b51200000000L, 0xd127656ded4aeeL};
uint64_t A[8] = {0x7306bbb8a15a8e04L, 0x8f02d66c01def11dL, 0xd63291c8154a67e9L, 0x7c6e85f3616f1ccfL, 0x1e787b17c6e02971L, 0xa4194c68b7b0ee5aL, 0x48bb709e959aa2bcL, 0xdc645794566e4359L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xc5421421bfcd1ab2L, 0xc1232cb0f1c22dd1L, 0x4b797085d609844dL, 0x72f7730db995c297L, 0x87a75f21f419c3f0L, 0x667a49f63c88d528L, 0xe8cff97c26e664dL, 0xf1b076d521a6c61fL, 0xffe52007a973c1c6L, 0x69fff72436c15b9eL, 0xeac7679285b6cee7L, 0xa65fe36553d9ea68L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 158;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x70f47512bb149c73L, 0x4122af86feb3e0eL, 0x93b884c10bf07590L, 0xc15e092f3a34f218L, 0x31e06b000a35569dL, 0x8dd58316004fc627L, 0x79b45dfe152d7c0L, 0xc0565572332988d1L, 0x2914ff36d6eb00c7L, 0xfffffffffffffffeL, 0xd6eb00c800000000L, 0x12914ff38L};
uint64_t A[8] = {0xbeab1712a6b7b41L, 0x4cf00f7286986417L, 0x7e5fa880503608e3L, 0xdfb258a6cecf99a0L, 0xb0bd6b72114b64bcL, 0x1ab4e30f608fb025L, 0x7ab0590d97c21cdcL, 0x7cca0f74c4dd4a53L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x767bb32509c7bef8L, 0x347f67201c3f96caL, 0xf18d83a6906d0ed4L, 0xf6cdd7e20cdeb6e2L, 0x5cffe68221ff0fbeL, 0x90309afb1ca897feL, 0xe74305976d588a47L, 0xa47f154e01acd14eL, 0x606a2510ede13a8aL, 0xc1e649b3c8a14c29L, 0xcdea82e78b569cc7L, 0xa51eda5781a82c21L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 159;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x611af540de4573dcL, 0x5cef2645ad0a6f76L, 0x97e6b0d8a00f7cefL, 0x4bf333748c4c1935L, 0xa5cca9b760d3667bL, 0xef594ebab50a370L, 0x3ea442ae22f5bb23L, 0x6f833d2ec1cd4485L, 0x46307fffb9cf7L, 0xffffffffffffffffL, 0xfffb9cf800000000L, 0x46308L};
uint64_t A[8] = {0xbdc3f5804558c906L, 0xbe50b32eac05abe5L, 0xabf8eec667de9f04L, 0x30c099e05035eac8L, 0xc2a65a2b6251ee57L, 0xaa1010f7e96e7986L, 0x9f80c4fdf2efb104L, 0x22e94574db40cdfaL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xdb09c264c62b6407L, 0x963988e779e578cfL, 0xb9ef7d0aff0bf0bdL, 0xc99a645965f65df4L, 0x9a68a3a2ff308635L, 0xe19c66fac477834bL, 0x4a07e93fd684835eL, 0x34c7c52890e9353eL, 0x288e429218a826eeL, 0x9e33315ab0036b9eL, 0x912d377f2e8d7ba9L, 0x8e5353a47fd33439L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 160;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x54955d0abd6784f1L, 0xa5ef22c48fac0b04L, 0x4fe61dd86a57e0f3L, 0xdfc9e353b994adabL, 0x920d9b795ffcd9ddL, 0xbfd212514cc650d6L, 0x61ca8b3c2376e060L, 0xa92165867c4c58ccL, 0xd8eaf208269c1519L, 0xffffffffff870722L, 0x269c151a00000000L, 0x78f8ddd963eae6L};
uint64_t A[8] = {0xb7b80a3b92f33f24L, 0xebb8c6eda66109f4L, 0x3d4e414d5ae125d0L, 0xfe4bac5d667b36a5L, 0xf91df8af155ce79cL, 0x36c0fc867a2482aaL, 0xc67961734171152fL, 0x7ed40f8766c8520dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcf6d5908bd7c56fcL, 0x88898415eb00dc46L, 0x9d126e731933b5d9L, 0x9da8d3a9674900feL, 0x189154eb8cb08545L, 0x9b26cd1374fb6caaL, 0xaf1897fa01f69d8bL, 0x9e6e408383f87444L, 0xd9d8422226600cadL, 0x275a5461da3d4fadL, 0xf0ffd828c78f3fb2L, 0x8abc268337371c18L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 161;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8d97fd53554fa366L, 0xb932d0c175274655L, 0x59d18be925a81aefL, 0x80ee662fad29cf9cL, 0x18f61f3cdef3f99dL, 0x4976126318fb05aeL, 0x41a471e4e93046f2L, 0xad5cb247cd789d17L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x2f5bed61b2bf8527L, 0x39312685ac014db1L, 0xc5aa4ee0d0363ee8L, 0x61b99e9d8592721aL, 0xf88d20c387b380dfL, 0x6ddc3f7eca0ee124L, 0xaa23bb50cd21793fL, 0x8242163c46de25a0L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x2aed1f8db00a6af0L, 0x99d9cd8514fcd49eL, 0x5c378ca1cc6c4713L, 0x7344f6f6053bf093L, 0x2071a82163fbd507L, 0xff1af1449b1be572L, 0xfeb0ad1f9ab970bdL, 0xe15880c2b7aa08e9L, 0xa1c3f00d5d6fe1c1L, 0x7ffe55c436da075cL, 0x6bd8c2f8aa8e23f8L, 0xe0cb386dd868a27dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 162;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x7d0a05270a803f41L, 0x7732f696695cfd4fL, 0xec3d8bb3ebcf6477L, 0xb761317f5251fa35L, 0x7882514918cbdb1cL, 0x4e0f760463c9e62fL, 0xe1ffc7c8efb434caL, 0x753981d9aa9ea355L, 0x61ffffff9dL, 0xffffffffffffffffL, 0xffffff9e00000000L, 0x62L};
uint64_t A[8] = {0x1b8e99ec73674fd0L, 0xdd2db1ac1c655c22L, 0x6961af51e2d8306bL, 0x8be27de7f56e210fL, 0xfb1256c27d874a2eL, 0x16f5d1e9cfdaa431L, 0x8fc19cbb4701173dL, 0xfbfe9539b70e2b92L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x9a8f7251a7a9c000L, 0xedbcca02a307ea74L, 0x48e6e7743c9554c4L, 0x4241eb41e8092ae8L, 0x39d0a69f9d14637bL, 0x2ef0f3c31f56c7d4L, 0xc00767219abcb9eL, 0x1ff5f3f1469ce778L, 0x702ca15cc7e3cc50L, 0x207659a373e1ae6L, 0x3dcff26694bd8ff6L, 0x650cb8b641d4b740L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 163;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x3845c706bf1af378L, 0xe5923ab530107b56L, 0xef711a45f62289dfL, 0xf7cc6c9cd8747014L, 0xa7f4a3e3b1e9669bL, 0x1559c7f8a3abedf3L, 0xa2952abc1624f023L, 0x8046ed8801a1fa6cL, 0x1f5bffffda168bbdL, 0xfffffffff9728bbdL, 0xda168bbe00000000L, 0x68d744225e97442L};
uint64_t A[8] = {0x5407a49b4faa0cf2L, 0x7eb23d3000f5ecf8L, 0xa2db87227dff4d2L, 0x6f0021dca8ee51c3L, 0x3e855bd6d766cb88L, 0xf50f8d1d5397f0dfL, 0xd0b1f024322e5746L, 0x3f859e44807206L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xdebc06f289fd8ddcL, 0x520e36af452eb615L, 0xa9893eda2dc5fc92L, 0xa8eea6b0efa04586L, 0x77e43a6d0419aac1L, 0xfbecb2e325ecf490L, 0x2bd44c0fd79b5b7bL, 0x5e3b0671cf52bb6fL, 0xb7ff7e07eb1e1fb1L, 0x38535cea55b77264L, 0x5f8c88fd7e761aebL, 0xcab10e2c57f3e8e4L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 164;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xce4a5a002a148f14L, 0xf4515cc2e75e633L, 0xf05052f2d67c992cL, 0x6e85bc70b66bd186L, 0x3b8304539f133768L, 0xb3e3e323ac1d2f1aL, 0x2db9f111baf27adeL, 0x335872359cac8cbeL, 0x92cb03ff618f31acL, 0xfffffffff45a35acL, 0x618f31ad00000000L, 0xba5ca539e70ce53L};
uint64_t A[8] = {0xb2be2bcbec5c898cL, 0x629b728b79cc50c3L, 0xc4aa5773a020613fL, 0x45ffdfe932db6849L, 0xdc92f1abb243be2eL, 0xaf03c05fca655b38L, 0xbf279c7062e44081L, 0xae9f4f976943bc03L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x90f284f56181bdaaL, 0x3407a91ed8ed6f23L, 0xf72e7fa5210d9d2dL, 0xe267ca20894807a4L, 0xf5f63805f4af067fL, 0x95b6245a310ac270L, 0xe0cebfb8003479d9L, 0xb99af73a27b6b075L, 0xec36ad4498b5344bL, 0x5386c1dfb13ab140L, 0xace73798f1c19a94L, 0x8216b7e17acd3da6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 165;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x4b43dc542a720bd5L, 0x9553438211c6274L, 0x7c448153752fa4cdL, 0xccbf22a67c30b606L, 0xee8f5f282d8817afL, 0x7481ce813c9fb654L, 0xf21f374f9a7c824cL, 0x4e0a3f471ee813f1L, 0x430c0fffbcf3eL, 0xffffffffffffffffL, 0xfffbcf3f00000000L, 0x430c1L};
uint64_t A[8] = {0x633882d09d70b2fL, 0x751a305fb9992f1dL, 0x7e062c54bcd8ace8L, 0x52ebbfcdf7150d28L, 0xc9a8d89c7d00571eL, 0x6688e25bf90134ecL, 0xb8c44a8ed98d1f32L, 0x404354ed7f4ab63fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x683333e1aeaf78d5L, 0x975e72a8b3993677L, 0xc70843fa09122141L, 0xbae66fc046f3c59aL, 0x5c6c214388a7a776L, 0xf6e11928273a95eaL, 0xded757617e87f854L, 0xf82895593536641L, 0x95e1cd28918fd2eaL, 0xf86e2c3d4396e9c1L, 0xfdee0b786f6caaa6L, 0x63159470c403ba11L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 166;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x948dc4f8b1fc87b4L, 0x8ef5689d3cf7600dL, 0xdd3cf7e7473017e6L, 0xe2f73c696755ff89L, 0xf38ae8914d7b4745L, 0xfaecedfd0c9803fcL, 0x2d921ca298eb6028L, 0xd9e9fe814ea53299L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x45d510091bce75f0L, 0xf0f5d282269422c8L, 0x31a270d5664cea76L, 0xc1bd40fd0ebd1073L, 0xc9dc5cfd2c615844L, 0x9ec4820e2046a44fL, 0x72370a800e0bdb56L, 0x3ca45cb5b3b8f8d9L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xde62a1ac31a99038L, 0xf8f55d4c77dd01d2L, 0x91a2b2e494fb0585L, 0xc7f23c5362686d34L, 0x3e5920355c9d33a9L, 0x962f04d226a51135L, 0x89ad93b085d55293L, 0x8509b0af37ac6639L, 0xb1474b0f69d1ee3dL, 0x620069e4e99cc2baL, 0x546578ef1f1cd28fL, 0xdec60493a76710e9L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 167;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xccb1bd68311fa6bfL, 0xaf844ef3d8c34475L, 0x7b831e70a0939d01L, 0xaf05cfa35dc6b0b5L, 0x40f1d846956003acL, 0x66119acd9e0bdc2dL, 0x45d4d47be9bef5a1L, 0xa2e25edbdaa1eb73L, 0x8b98afff74674L, 0xffffffffffffffffL, 0xfff7467500000000L, 0x8b98bL};
uint64_t A[8] = {0xe22b104ad0f67420L, 0xbaf5500801638fa6L, 0xfe4601e2b5bf98aaL, 0xb2e97c5f8d1e0c72L, 0xa09a2ad2d0d67a2fL, 0xcf3cbad5d5c143a6L, 0x57b4042b9fcef2dcL, 0x2b55741691d9fe6fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x72655fe7ea5f2342L, 0x71f453b06ba96222L, 0x4f289ca4d57e69daL, 0xdf41e94fe53a3e32L, 0x4a9835bb4d96ad2eL, 0xb663889ad1648ae9L, 0x350cece9161ea192L, 0x5131bea947a20410L, 0x9fe95e2a2dbc5bd9L, 0x569230ace87bb892L, 0xc110e45115d34e11L, 0x4969576f9b95e14fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 168;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x608573f01d4792f5L, 0x95f12fbd9521945aL, 0x5305550cc65c7467L, 0x976f8943eb14ae2bL, 0xe5a4d4ace2b77e77L, 0xaf1b5f390f5b0e83L, 0x6a81d85841a135abL, 0x3cfae6ab3f62f23bL, 0x4052083fbfadf6f1L, 0xffffffffffffff31L, 0xbfadf6f200000000L, 0xce4052090eL};
uint64_t A[8] = {0x480dbc1bdb128292L, 0xf4403cdc248a5658L, 0x326307428f89526L, 0x3daf9a43c81445f2L, 0x40613619d75d53bcL, 0xb13f2e85b503b962L, 0x725f5a062297d5b0L, 0xd4276cd13fed7f56L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1c84d6cfc1ae69ebL, 0xdb1d3a13ded20aaL, 0x8cc3bc88b91f2bd7L, 0x7efc6633140b77daL, 0x31120e5c73c48799L, 0xf68d944edbeff37cL, 0x35dac718c791a47dL, 0xcb6d6ddf7b2ac766L, 0xabc3a7bbf753d95bL, 0x1f4779660f915adeL, 0xc52eb444429b0ee0L, 0xb7fb85e94d321766L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 169;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd83cdbe4b0cdc8bL, 0x5543627b60fa2969L, 0xdee9b49a7fbca4a6L, 0x9c56f6686507ed0L, 0x7d535ee00de9dd06L, 0x1bd745d87f714f97L, 0xb8b50909061de6fbL, 0x57820068f4a96b3aL, 0x1affffffe4L, 0xffffffffffffffffL, 0xffffffe500000000L, 0x1bL};
uint64_t A[8] = {0xe94a016c3e489b9aL, 0x4c0dcd300855ca85L, 0xed8e08d20eebc2e5L, 0xb358109f2f4b170aL, 0x4b5123a73a5b4568L, 0x581e5ff924197743L, 0x9860cd99345cdd47L, 0xb3ac042d1ac3e740L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3293c1e0a74d59d0L, 0x2627e23178e8fd38L, 0x42ed300ea9aa153dL, 0x917ce486f6176f78L, 0xf321f1133f5f2740L, 0x357574c6a3db8ca3L, 0x4bb03b107a68aee6L, 0x93fb62cf28850bfcL, 0x6824f875de383fa4L, 0x8b0bd10da1cff91dL, 0x4ce9dc56c004a569L, 0x24333f610fef4bfdL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 170;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x68f66263f8fcf831L, 0x29d70d71caa56536L, 0x6fef91b432c35529L, 0x19171b6038e29235L, 0x4012a2ac282e7da2L, 0xcf53def4eccadb8cL, 0xb79563ba0a44904aL, 0xd21ace96f226a66fL, 0x6ea58e9e915a31ddL, 0xffffffffffffc07cL, 0x915a31de00000000L, 0x3f836ea5ce22L};
uint64_t A[8] = {0x254a4a3e09ba48fdL, 0xf5f9a498bf1bfdeaL, 0x7c18faa630900f7eL, 0x113542810b0284cdL, 0xe97fbab46827f334L, 0x5b7d6c595db8b18eL, 0x669025d6306e5844L, 0xee79ebb98c19a4cbL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x9f678b8fd97d755cL, 0x658693a284a2af0cL, 0x185ee38923ce964dL, 0x51b96455d5bf9306L, 0x6338223c9ae5b4aaL, 0x3f9c01f04fd9542fL, 0xb4c392f8017325abL, 0x17e1f19168a1a799L, 0x1834e5304f966c0dL, 0x4e16d50bab6dcc49L, 0x34afd61e08ca76e9L, 0x2170e27c59c724fbL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 171;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x660edf902355ed17L, 0x1cb9e62635c37fbL, 0x7a619b6cd222f819L, 0xb4faf459c42f8027L, 0x9ef451b887674f84L, 0x8d0ef4e5c56a617dL, 0x8893f2f973bb65d2L, 0xe185bf8bd6536acbL, 0x16a973ffe9568bffL, 0xffffffffffffffffL, 0xe9568c0000000000L, 0x16a97400L};
uint64_t A[8] = {0xf9e52a3c3d09587fL, 0x4df9d7e007e02f99L, 0x56b54f114a88d0ffL, 0x8bd26aa0267ffedfL, 0x28abcab71f0d0a08L, 0x41011586e26e500fL, 0x117b7425690e41d3L, 0x1877d8811bda67eL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3d7486cde5e84beL, 0x190486f62e4a3649L, 0x2c0b88a4ffe8353bL, 0x4d8452aa44622099L, 0x99e012c0aedf93eeL, 0x87460b889af9fd43L, 0xb6d52ff680aad7a8L, 0xd44f49a5754c5a8aL, 0xb22d7b3aa7bfd4c4L, 0x6bc8ba3ca4113dceL, 0xc7de843349f76f78L, 0x9d2f29a88925738L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 172;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xae5e63e820e55d8eL, 0xa7d1484cfd501eeaL, 0xd3a6d09612e55479L, 0xc2f7251ae074ddddL, 0xf6d7d3a8bd6214b6L, 0xf125c7ed1513d22cL, 0x5644cdbc6aeb652cL, 0x5e9a815ec6b4d9fcL, 0xe5c87fff1a377L, 0xffffffffffffffffL, 0xfff1a37800000000L, 0xe5c88L};
uint64_t A[8] = {0x863adcbfc3e11936L, 0x132997833c5875bdL, 0xc66fb8e48cec6857L, 0xb9ec70c15113985fL, 0x2dbe3b667dc96eebL, 0xcdc946093e60978eL, 0x17495e3dd74c9d3bL, 0x2babf31ff018f49cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6bfba4079309f28dL, 0x232838d65c3e5c2L, 0xc11065826313667cL, 0xba8f7f1ba6291cc3L, 0xbde7b2507d9061L, 0xc6a7843da494ec67L, 0xa57dfd3c5ca8f10eL, 0x9a40e7a5db87cb5L, 0xf61941e6a30d3b69L, 0xfe2cb1ffe8ad7f7fL, 0x22766421169b95d9L, 0xcf56726883c06c39L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 173;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa2139f4161139993L, 0x5afdd636e00bad01L, 0x32a8af03ae81f606L, 0xa1867be0104cc3dbL, 0x6a68b2b2176b3d50L, 0xd5e1faad1d82c4L, 0x12f1af02ac5d5f73L, 0xcfbd2f21ab75a918L, 0x247dbc7fdb82437fL, 0xffffffffffffffffL, 0xdb82438000000000L, 0x247dbc80L};
uint64_t A[8] = {0x5407a49b4faa0cf2L, 0x7eb23d3000f5ecf8L, 0xa2db87227dff4d2L, 0x6f0021dca8ee51c3L, 0x3e855bd6d766cb88L, 0xf50f8d1d5397f0dfL, 0xd0b1f024322e5746L, 0x3f859e44807206L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xdaf43fef887ff347L, 0xe6f8df1824b30aa0L, 0x6d64e2caa1f0b9b3L, 0xd0f3db55043dc08fL, 0xc0fccc156390b716L, 0xbe9be344c41028d2L, 0xa6518b807adf618eL, 0x933527794679b2bcL, 0xdb5c3d6092f63372L, 0xbe31c17faa037147L, 0xd96b051d221428dfL, 0x18d9d866fd40a0d2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 174;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x68a850991b58242dL, 0xb3d7e772d038b233L, 0x3b01c5b8126576d8L, 0x58d62bab69b6dd07L, 0xba9f2dbaf9b283bbL, 0xbf126005973f4859L, 0xec342960a28c6706L, 0x9737c93286f3afbcL, 0xfbc49c17ff5eac9cL, 0xfffffffffb2348b4L, 0xff5eac9d00000000L, 0x4dcb74b00a15363L};
uint64_t A[8] = {0x93dd30692eb231d1L, 0xa39f471f32cfa731L, 0x62f7ee7e271be610L, 0x24f77778117311eeL, 0xd42c2714ffcea877L, 0xcd80cbe14660ab67L, 0x47bd736b9e83ef82L, 0x76e3740442e49996L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x65a6f0b0bbe6bc64L, 0xd8db049cea09158fL, 0x760837fa1d5cd47cL, 0xbf999eeeabe9186eL, 0x1eb2c335648afeccL, 0xcf88ed4094bb34c0L, 0x165a4b2dbeca695dL, 0xca8e2f05a247125aL, 0x6bba6f4c2376c8fdL, 0x726ff0fcb8b420d9L, 0x2c568dc9a136c738L, 0xa197147c5aa3373aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 175;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xeb4e0bedaf83eb13L, 0xff69ed4bd3090ad0L, 0xb916baf2d49c06f6L, 0x1a82cd535b92e04eL, 0xeff85963138cfe77L, 0x212e9643d09e2997L, 0x9d489489f849853aL, 0x5f2896f041e52a1L, 0x57ffffffa7L, 0xffffffffffffffffL, 0xffffffa800000000L, 0x58L};
uint64_t A[8] = {0xfd10d4229c2a4473L, 0xd255f5c688011591L, 0x6168ae5f30b59dfaL, 0x6f939d68a2be35f5L, 0xc9594125c2f30c3dL, 0xfaa6fa91bc6665c6L, 0xc1cbfb07ec4e60e8L, 0x5f41d10cb649b4c6L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4210804f6e818ceeL, 0x7f6e701a6407daffL, 0x74e05448652d0c0aL, 0xe3c81536ff41e704L, 0x86d8e1ffcdbdf16cL, 0x3de9c182585aa6e6L, 0x597012368d327210L, 0x7a325569e12b02f3L, 0x1b1611572e69471eL, 0xd44d82abb2a0326L, 0xe55749db7317bf9fL, 0xd9d7779e6a9eca5cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 176;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x2931445e086f7164L, 0x2ddf1ab2d20f7ee5L, 0x57905fb7d52b640eL, 0x9a46b49b10c1a213L, 0xb8cd230d2194f376L, 0x8472d27b77f51d9L, 0x3a6d57c809d5690fL, 0xa559bd9170b70803L, 0x88d7dbff772823feL, 0xfffffffffffffffeL, 0x772823ff00000000L, 0x188d7dc01L};
uint64_t A[8] = {0x76b85af13143ff6L, 0x25e08eed9e9aa27fL, 0x3e3d0488ffc51120L, 0xf8c81b242528c884L, 0x418e685027128311L, 0x63ac37d528a681efL, 0xf0a07a9732ef1690L, 0xc7fe6aa567d1367fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7c7a8489376df84aL, 0xc17a15ecb86b4d24L, 0x59aa9bfe47eb5c93L, 0x77601d4042b67e9cL, 0x9656adefac03b645L, 0x5bb26cb053017838L, 0xf600e68bd9473121L, 0x847bd7d906d0492dL, 0x299299787f4ec3a3L, 0xf4dbac34891fe234L, 0x3764e13f45e1e3cfL, 0x178812df27823L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 177;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x31b2004f71c85684L, 0x28168548f0fc1e1aL, 0xf033ab73e74de5afL, 0xc455ef66097254d7L, 0x18f0deaad4d2a242L, 0x4ca8ea47ebd58c24L, 0x1b996bf120e2ff27L, 0xae76c66e0dbb96d0L, 0x3d08ffffc2f6fffL, 0xffffffffffffffffL, 0xfc2f700000000000L, 0x3d09000L};
uint64_t A[8] = {0x4b9a67c522358b19L, 0xdb689ae4d6a34ac0L, 0xe71ae2779a3088edL, 0xd1db1ff509ec0582L, 0x802c066f38243ea0L, 0x5296b228a6e2d112L, 0x564a809d50034236L, 0x48bb5e47beb21fd5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x639a10f743ebf5ceL, 0x51141e7923509835L, 0xa0e05b35f6f0a7d4L, 0xb77f09ac6b1db9c0L, 0xee07606f8567f82bL, 0xdbaf4935a24ddac0L, 0xe021a55473e3b9b5L, 0xceae05b03e4ac36fL, 0x15010568574fe7eaL, 0x9df81070e2a93b3fL, 0xd5419acb0f369de0L, 0x3c6507eb8580a0b2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 178;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x44210c4715ecba77L, 0xefa47f2abbde5a26L, 0xfee52ad892a989c2L, 0xf37d3ec6c692708dL, 0xc88a1ee093dbe19L, 0x524a17493c6bd3ceL, 0xa913d3847f65477fL, 0x82f2578db893a41L, 0x1fd10fffe02eeL, 0xffffffffffffffffL, 0xfffe02ef00000000L, 0x1fd11L};
uint64_t A[8] = {0x3ebac409b05772d0L, 0x711e5e840cfbc417L, 0xad7808ce1eefbb4fL, 0x33a00a3d970a6c2aL, 0xdb000adf2d9f7069L, 0x51c6cd66d6e20c17L, 0x93ca59316f6b93afL, 0xf48749e3cf9476abL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x8f90deabfd513551L, 0x94209461ab4a498fL, 0xa736c90cce4ddb3L, 0x8d3ebac9a91bc2d3L, 0x6cef806f95af5ea8L, 0x70f6fb42c1962da6L, 0x1de34f643b4fbe7cL, 0x50a3557e2318b1b7L, 0xb5b7d0c71377467cL, 0x3a74546f8a678470L, 0xbd845aade3ea68f6L, 0xa96b4444a8d11919L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 179;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xe05b3080f0c4e16bL, 0x2cc09c0444c8eb00L, 0xabe6bfed59a7a841L, 0x75c96e8f264e20e8L, 0x86659cdfd835f9bL, 0x2b6e019a88b12f1aL, 0x56af7bedce5d45e3L, 0x1eb7777aa45f3314L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x2f5bed61b2bf8527L, 0x39312685ac014db1L, 0xc5aa4ee0d0363ee8L, 0x61b99e9d8592721aL, 0xf88d20c387b380dfL, 0x6ddc3f7eca0ee124L, 0xaa23bb50cd21793fL, 0x8242163c46de25a0L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6d6b10710c490eaaL, 0xf4ac8213ed07d7cL, 0x2329dc445e004369L, 0x7702698c3f7db1c5L, 0x74c05aeafd2f5af3L, 0xcad04fb9983b93bfL, 0x5359e001de882ca0L, 0x7125fe553ca64820L, 0x4f00bcdfc1faa3bdL, 0xc708a81673862b1L, 0x19c38ef4768e96a6L, 0xebf0300e5f445131L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 180;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8046e2575843b82L, 0xe3ff8b6720ceab86L, 0x5239c24160828f13L, 0x592ad0d46fdaa429L, 0xad4004ce43cd213L, 0x76615b4db779168cL, 0x63bf21c96d298e73L, 0xe7e23b4acf3c9025L, 0x5fffffff9fL, 0xffffffffffffffffL, 0xffffffa000000000L, 0x60L};
uint64_t A[8] = {0xc3314eaed2a2d2eeL, 0x66a7e2fb5553fcbcL, 0xccaae4fc6868dee1L, 0x55744795b1014962L, 0x600653c217732d4cL, 0xd6d7564e68c15c6bL, 0xab9a79fc0723302cL, 0x2593d793f3067d6fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x75448c0d82bcacdeL, 0x31e7cb7615ac478L, 0xacdea3a8eb24e4caL, 0xd2f91ca9e06f6b34L, 0xf67bcfaf6a441079L, 0x7c5c266574fd268L, 0x28a8a26dccc85a9eL, 0x1bfab3be6dedeaaL, 0xa49918a00df1cdaeL, 0xf86cb941867478a4L, 0x3d9c5ded8fec5a60L, 0x565685e76cb7bbb6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 181;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x51867fc4383ea6a8L, 0xe3dfc579d41b6ce9L, 0x1830271f9ea11342L, 0x9f6259874e9e6a67L, 0x52533292e64582faL, 0xb5f0afb0000a0888L, 0x6c1dbd1296624058L, 0x36937fae92a2781aL, 0xb8747c423ade0ca4L, 0xfffffffff35288e7L, 0x3ade0ca500000000L, 0xcad7718c521f35bL};
uint64_t A[8] = {0x1b8e99ec73674fd0L, 0xdd2db1ac1c655c22L, 0x6961af51e2d8306bL, 0x8be27de7f56e210fL, 0xfb1256c27d874a2eL, 0x16f5d1e9cfdaa431L, 0x8fc19cbb4701173dL, 0xfbfe9539b70e2b92L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1a5118d8555ef70cL, 0x55855deac80fe1caL, 0x6a08502d1df34c13L, 0x1319694c295a0dddL, 0x2b6e072321759be6L, 0xebd35050337186f3L, 0x59cb264c0671d1b1L, 0x67a1812767b5cbdeL, 0xbd90741b3a19a406L, 0x50dd5b19c15c6268L, 0x6bd7caf36f89a741L, 0xdd12ecf61d52c1abL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 182;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xdb15e4963d5baeb1L, 0x9c30c6422b2f9c49L, 0x719a87be5a0ec9ceL, 0xa2193bfc266f85cL, 0x854dc9d595105f9eL, 0x2b4f0c7877eb94eaL, 0x4788522b2e9fdbb2L, 0x83c3139be0d37321L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x4b9a67c522358b19L, 0xdb689ae4d6a34ac0L, 0xe71ae2779a3088edL, 0xd1db1ff509ec0582L, 0x802c066f38243ea0L, 0x5296b228a6e2d112L, 0x564a809d50034236L, 0x48bb5e47beb21fd5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x40ab20634ad8a237L, 0x7bc88ccf5c53bdedL, 0xc8d4a09fb7f3898L, 0x79271658cad201e4L, 0xeeefc88bbb26fae4L, 0x9a1e5f61b72f8facL, 0x220c261d386ba2a3L, 0xfb34869a06187089L, 0x7084832de4d9dc69L, 0x3f37d4a2ab73ae77L, 0x75805aba4021bf1fL, 0xc7b98c3547850d25L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 183;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x87d980bbb0f958d0L, 0xac1c29f12544bf9eL, 0xafa28bc9d968760fL, 0x3ca12e5baa87b8ecL, 0x4706762d5866bc30L, 0xbedd23b12204c06L, 0xea5302ed5c91ad71L, 0x278853942f532e82L, 0x39aa3fffc655bffL, 0xffffffffffffffffL, 0xfc655c0000000000L, 0x39aa400L};
uint64_t A[8] = {0xe7f5ba6f2554f427L, 0xdf48518b3901ff96L, 0xa828c36c1d4e879bL, 0xef6c4ca1424432edL, 0xedc19f099a5676dfL, 0x8bf2891468410bffL, 0x27cf306a14944795L, 0xb6efb4cd4463768L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6a54c39199b65a8cL, 0xd8e1a8bf779a8a1fL, 0x14603c6c8d1346aeL, 0xd14e2efbb8e4c4daL, 0xef621050cc69035dL, 0x47e2337c528ccf6cL, 0x890b7daafef55ee6L, 0x9274ff142b72810dL, 0xa137d476bdb5e826L, 0xa93589ffcd671f1aL, 0x897029f1d018db6aL, 0xf1f287df56a78514L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 184;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x276515f7bd22ce0eL, 0xca354d7a6a94b957L, 0x531923482ee1dd75L, 0x378c7067abdf028cL, 0xec168826ceeb0f34L, 0x1817c14d845b11caL, 0x764cda227eb7977dL, 0x5a3ce157e90ce287L, 0xdaf26aff250d94L, 0xffffffffffffffffL, 0xff250d9500000000L, 0xdaf26bL};
uint64_t A[8] = {0x2b9131acc0130435L, 0x97a689a71742557cL, 0xa81ea03df9581714L, 0xc34ea0250f6667dcL, 0xd734003dee5d1e66L, 0x7bb0772a8b6e0589L, 0xb1f409df762e3ef3L, 0x60f7817684aa164dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb745814f12148154L, 0x6fe56ee1c2d7e112L, 0xcbe5133f969247d5L, 0x859be7ffe5bab28aL, 0x517ffd50fce685e6L, 0x82f393a50891d73aL, 0x6d9105cd643962d3L, 0x852e9874ff847d32L, 0xf11296d485987aa6L, 0x66e44985e8e9f9d4L, 0x73630f9e335708c8L, 0x61645cad5de2cdfbL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 185;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x57884bbc1df3c833L, 0xfefab45dd45d76dbL, 0x97116eaaf30e0724L, 0x99a74f1e96b39699L, 0xf031bc993bdff749L, 0xa7582aefd08a3612L, 0xd479a2e2a1f701a1L, 0xe95611229270bf47L, 0xc3ca78b83c34cc05L, 0xffffffffffff44beL, 0x3c34cc0600000000L, 0xbb41c3cb33faL};
uint64_t A[8] = {0x8a7b94a8d2ba7cbfL, 0xb5073c46c521afacL, 0x7cc470a1295a5fcfL, 0x5d0302625fccb507L, 0x773c2a475c4c5a9L, 0x462440ee1bc9f085L, 0xda46dfac5c6cef71L, 0x19fb9a08eeb85a69L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x53aa95b867a68779L, 0x49a823954cb77f4L, 0xb5fd7feced82184cL, 0xc4d4d0fb3f7ceae1L, 0x6bfa3842b8276dd9L, 0x9c12b20529d804eL, 0x96a524327ab2a94aL, 0x8e1c78bdf0b43af8L, 0x5a305b7cba259738L, 0x314eb31f5ba8890eL, 0xb9595dbccb27c152L, 0x7083e6564db098d6L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 186;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x691d130e5b90396bL, 0x303a322d1286c1dfL, 0x1b3464c84e02f849L, 0x4b285a38389df1f0L, 0x7ad765043564aa27L, 0xe291eb7708669116L, 0xe9220cbf2a4354dL, 0xa8175b1e7d7ab5d8L, 0x156fffffea8L, 0xffffffffffffffffL, 0xfffffea900000000L, 0x157L};
uint64_t A[8] = {0x49b2a0b16a395853L, 0x32092e494617dd75L, 0xce614c2f83c516f2L, 0x40afd261d2a96d7dL, 0x735fd9b0767a558dL, 0x7c83d9d9520a759fL, 0xf34063ae496cce27L, 0x4270a2bd4b257a7aL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x46b3f352ba14de1aL, 0x66b67359f648f169L, 0xab51a1afc1dd69e5L, 0x6b2a2f0868ba11d0L, 0x1556f2994df0e2a0L, 0x33f0821a25553f63L, 0xd9d68f0638addb0dL, 0x6f3214c35b79985fL, 0xeb61d99ebfbc9435L, 0x4e22aa8f724e5a77L, 0x6714d7f431c6d7a1L, 0xd4aa8900020ababeL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 187;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf361fa3a981e64d9L, 0x91c514c62c09c0b7L, 0xb0c3fc56fbcb63b0L, 0x41c49a77220e7e26L, 0xb59092e0b35fee4fL, 0xf931db5e676c91b1L, 0x99ea16d00f4fda62L, 0xfd5edceb0255b912L, 0xac16c8df53e9371fL, 0xffffffffffffffffL, 0x53e9372000000000L, 0xac16c8e0L};
uint64_t A[8] = {0x9b1d73d30c074c77L, 0x7066b28e4e81f4aaL, 0xc693f6041e7a86d1L, 0x571b9ffe1b1ce20fL, 0x146428ccc2a6d239L, 0xe739711ae0613c3eL, 0xcac27df8a27cf75fL, 0x4f08c45d910349ceL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcc7e4ff576f13b1aL, 0x27c92115918e414dL, 0x287bfdbbcdb2fabcL, 0xadc087a1884ceab4L, 0x53d9c60f5b8dd7b0L, 0x85fa89e473fec1e6L, 0x6e30a29a432e0192L, 0xa932c972a7a7fb14L, 0x1e0e349954104010L, 0xc06e929fe3c9b2a6L, 0x6929afa51cbe9445L, 0x4600911ce78ab326L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 188;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xaa934b4fa63bf410L, 0x50e98913156600beL, 0x71b984cd2b03e9f8L, 0x6d1fac1a44622bbdL, 0x9a56146d3d419ce7L, 0xb56b4a249487516dL, 0x5b4d40de61867aefL, 0x6a9155ce36d1ef68L, 0x14640fffeb9befL, 0xffffffffffffffffL, 0xffeb9bf000000000L, 0x146410L};
uint64_t A[8] = {0x2f5bed61b2bf8527L, 0x39312685ac014db1L, 0xc5aa4ee0d0363ee8L, 0x61b99e9d8592721aL, 0xf88d20c387b380dfL, 0x6ddc3f7eca0ee124L, 0xaa23bb50cd21793fL, 0x8242163c46de25a0L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe48292b6651f726aL, 0xcf922ec1e2433457L, 0xb9af63680199a4d9L, 0x71fd9404819771ccL, 0x16c015c568a2a3d8L, 0x2f111b417f37b6e8L, 0x3660310b6fdf694eL, 0x3ae10ae8dbdb0bf5L, 0x83d6703e21d6f058L, 0xa2b695bbc9cce671L, 0xd74b94f401215b97L, 0xbc08e06b8c70641fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 189;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8890cc0452eb9c84L, 0x14957fb499ec6a18L, 0x51a4ebbdcf0fa9b9L, 0x96766c24df3fb26dL, 0x7207822b84b62cb4L, 0x865a0917ec12332cL, 0xcfb6895930879032L, 0x8c1d884c44c25676L, 0xc21cb8e03de346ddL, 0xffffffffffffffbeL, 0x3de346de00000000L, 0x41c21cb922L};
uint64_t A[8] = {0xb595d8a9eae3eff3L, 0x1fbf14715b64ea48L, 0x2c1fa02b57ccd532L, 0x13ad0573e9799e4fL, 0x9026eb180cd032a2L, 0x82128bb46643b150L, 0x818a6d8f4706304cL, 0xd93ef16f097c5ad9L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1f4c8b3191912554L, 0x58cd7e6343b93986L, 0x6f664e0543325c4fL, 0x2ed63293b344d083L, 0xaf9460c90b5dca5dL, 0xc2c051eccc99138dL, 0x13a3d6242a7e5afbL, 0xefe3c3f5532b443eL, 0x7e96fa2ca03cff8bL, 0xe5b694714a9189b0L, 0x3b1d4a60656ccb8aL, 0x7a6ca80f2fee58a3L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 190;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xd19ccb06951fb492L, 0xdea28c40b20fcd5dL, 0x1cb503dd07a790aeL, 0x5b350757dbd1e4acL, 0x7eaaec0384d6401eL, 0xcfcb8184f9d65327L, 0x20b5e89291add8eaL, 0xc049158a32782678L, 0xa65fffff599ffL, 0xffffffffffffffffL, 0xfff59a0000000000L, 0xa6600L};
uint64_t A[8] = {0x2d0f1be2b5577cf9L, 0x8decdf26c01ce141L, 0x7e28a0d562d7881L, 0x8218884b2f38e1d6L, 0x707320391e7826faL, 0x36925b3cb704a1fcL, 0xe77da7d78929b20aL, 0x747c0826cd4f4e7bL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x63a89c6a4767e3c9L, 0x8088ee6dbd0f538bL, 0x8766b27909c8f622L, 0x3d5da79f545bed6bL, 0x83731a91535622bdL, 0x7affd880ed4b4505L, 0xb84203e539e2cd9dL, 0xe3620d9677b012bcL, 0x1226a4a4eefd32b1L, 0x251251fdee057d44L, 0x90d41ef598e15ccfL, 0x94d98f0c59e646f2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 191;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8cb4b1bea9c85e50L, 0x95db20f38b9b28d7L, 0x6b192af4c47971efL, 0x81e6570fb6d1d8f8L, 0xe4f0d0bc760a701cL, 0x2b82840cbbed7474L, 0x20da14b3d7e6d11bL, 0xdacd294f210a6abeL, 0xd8ffffff26fffffdL, 0xfffffffffffffffdL, 0x26fffffe00000000L, 0x2d9000002L};
uint64_t A[8] = {0x47b8c90e0ec452b0L, 0x8691f46ed9af1fa9L, 0xda120f3433f2d27eL, 0x160837d249afa40L, 0xe0053424c4c03fc6L, 0xabd0d5874b2e52adL, 0xe28134da897595edL, 0xc9d2fe827d859fdcL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x4adb7eda704d73adL, 0x28127a04160b2a17L, 0x8e35b4948563957L, 0xbd0438eda486acb0L, 0x23e0d2e8d3cc8d76L, 0x52d2b71a1d3d0688L, 0x2afe63ed5a7bcb8fL, 0x46596fd178f104b6L, 0x602d9d21e15d6b23L, 0x1da1d3cfd7beb7a8L, 0x26c0798e1ee7b08bL, 0xe1db3c4825588479L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 192;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8a64b4e39eff803eL, 0xb30854780959d1a4L, 0x64f68bc43bed57d2L, 0xf8c14d1cbc7ac1d9L, 0x46ed5256394245dL, 0x252aa59b47e7c81eL, 0xea01a593c8d1589bL, 0x859fa43b3da555acL, 0x2253ffffddabfL, 0xffffffffffffffffL, 0xfffddac000000000L, 0x22540L};
uint64_t A[8] = {0x972522c5025fd739L, 0x2adbf1bb0fc3ffb7L, 0xc0a896a1a2f02abL, 0xda88de243da1658bL, 0x65045adc6074841dL, 0xac9f431251b238d3L, 0xfacd067ee9eea7b0L, 0x486a43b391ce223bL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x6a80895c4459fef0L, 0x7751d21ca56603f0L, 0x52e6a0c0aa61e290L, 0x23235e831a5accdeL, 0x44bed57bd02c28b6L, 0x284a29840e4d08feL, 0x934f64d4d8c67298L, 0x98d545387a1b9001L, 0x6e86ec2aef6849ddL, 0xd947a410a927b8eeL, 0x73b51398e7cc1e8eL, 0x2f345a7f8ce7786dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 193;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa0b71a105299b151L, 0x9af21b3551659875L, 0x5d2c9c4dbaab7661L, 0x56b245f2364cd576L, 0xdba3d13816ca966L, 0x9beb14b642e948a5L, 0x9464549cd3184525L, 0x451d20624191bf0dL, 0x120fffffedefL, 0xffffffffffffffffL, 0xffffedf000000000L, 0x1210L};
uint64_t A[8] = {0xb2be2bcbec5c898cL, 0x629b728b79cc50c3L, 0xc4aa5773a020613fL, 0x45ffdfe932db6849L, 0xdc92f1abb243be2eL, 0xaf03c05fca655b38L, 0xbf279c7062e44081L, 0xae9f4f976943bc03L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1a79fac11bfb07e8L, 0x2ad57e2011f137a5L, 0xb4841db7f8f1fe54L, 0xbd193c5a13a255a0L, 0x77a2005bf9213137L, 0x3187fa245d09b26bL, 0xd961b5a0e4d7625L, 0xa119fab8262340ceL, 0x8bf99134f861c339L, 0x3366c1bde079f4c8L, 0xd7a870b406ec1786L, 0x6a87d74f57679744L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 194;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x987ed824d49673c2L, 0x47f7b822e42efe12L, 0x227a90fd16b25ff8L, 0x42b8ecd2016b2f4bL, 0x307537ab7585169eL, 0xa2be4e39aa8de8e5L, 0xe63cb1ad7f98dcbfL, 0x482b60ca06712436L, 0x3c4ebecec20774ccL, 0xfffffffffe56339bL, 0xc20774cd00000000L, 0x1a9cc643df88b33L};
uint64_t A[8] = {0x40bb8a1ca9a92a51L, 0x112746e2f16e4f64L, 0x779bb091f4b4168bL, 0xb2ba97669274864aL, 0x37f260b9e557fe9bL, 0xf53a2212b22d0d90L, 0xe2f8e1c67da8af3aL, 0x592870011c59d7adL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1f99d66703d4f740L, 0x28ee9ecff319a483L, 0x59ab774fae8910c7L, 0x75a52c2022b73d2fL, 0x5cc8d5799b74030eL, 0xf1a4fa255e313b42L, 0x5a85cf4c76c3b91L, 0x4b4781265dc9c881L, 0xe908e6b7a80602a0L, 0x6993d16c83e0f3dcL, 0xde4c20ad58b56eaaL, 0x2f11fa179b08b2f2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 195;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xede8c475e9715ac6L, 0x6799079fe128f427L, 0x541f1d4e0cf9d69bL, 0x46231f174e1c1447L, 0xcface1c07b59e98eL, 0xa2741f4e350c0344L, 0x433193423b2b4e34L, 0xf9cea03149237a3eL, 0x9656d97064a2f329L, 0xfffffffffaf9cc9aL, 0x64a2f32a00000000L, 0x50633659b5d0cd6L};
uint64_t A[8] = {0xbc2905fdc2c72f52L, 0x67f5f05fcd47bd28L, 0xc4a70bcc9535ceL, 0xea9479cf0f52d533L, 0x4ef0c2e2a7fb0657L, 0x5d1379f69267bcedL, 0xcc5ccf9a29159b0eL, 0x6febb404d5e365f5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1a07ba5f7f08dac3L, 0xfdc3cd754c9b1fd2L, 0x7edfc55cda367368L, 0x20805dba47f366b7L, 0x5e760047c9402c1cL, 0x901cfba00e456808L, 0x9458c84b2ee2db6eL, 0x53a89ac983399aa6L, 0x583cb3045e111dbL, 0x121c800dd99a696aL, 0x7339fc680b832c47L, 0x91b3e9c6165c957fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 196;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x8b9f07efcce38e96L, 0xf9306e3ff60ecccbL, 0xf25fdedaeb5f43cL, 0xd22569b4cd8ccea8L, 0x4e14d4757b116d9L, 0x9d9e61d100481c9bL, 0x6b1c17a850560af5L, 0x31946a5fcc13db5dL, 0x342ab0ffcbd54efL, 0xffffffffffffffffL, 0xfcbd54f000000000L, 0x342ab10L};
uint64_t A[8] = {0x76b85af13143ff6L, 0x25e08eed9e9aa27fL, 0x3e3d0488ffc51120L, 0xf8c81b242528c884L, 0x418e685027128311L, 0x63ac37d528a681efL, 0xf0a07a9732ef1690L, 0xc7fe6aa567d1367fL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x834c58759a258edaL, 0xf3ee3a68b7a40dcaL, 0xc90e271d625c46c1L, 0x8133296c044b228bL, 0xf1144e46b8d1cf0cL, 0xfa2a35420f5da8efL, 0xce296dec970e8811L, 0x2b3e03292b9a58b9L, 0xab36f9d222b94e50L, 0x54b1607303e83cdaL, 0x37197200e149a513L, 0xe1a2d25c2b4e385aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 197;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x398ce99ecaf0ea74L, 0x64e06bfb7a8b1cd2L, 0xac9a9fb5eb3fc6a1L, 0x885172b68ff8ad20L, 0x78b0cc7f973e635L, 0x2d5f6c7f3762cf5bL, 0x88e68752ffc584dL, 0xbee7c6e0efbe84dbL, 0x6f7c52b29083ad4aL, 0xfffffffffffffffdL, 0x9083ad4b00000000L, 0x26f7c52b5L};
uint64_t A[8] = {0x80a698c8975ead83L, 0x90db4fbacc824d66L, 0xe3c23575a8e79d32L, 0xe8f79d0c8916774eL, 0xc07e51672184d151L, 0x5c15e89541c00f8dL, 0x49fa74271f568f63L, 0xf0d5282b6039e3a0L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xa4bc8eea8158aa93L, 0x2d4cfd17c4deb9c3L, 0xc2a744850e4fae8cL, 0x1bbe50d1d5423279L, 0xe73c5084288e1c57L, 0x520c64f9c68a3841L, 0xb67410acf90e39ffL, 0x4dfce77e369addd4L, 0x2d50217ac7436804L, 0x8dff9544bcc2af55L, 0x8b50bcabf12451ffL, 0x9daa81a272fcaa36L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 198;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x6a49c1b210f8488cL, 0xf383c6e080a94760L, 0xbc7d3d1b7c8a9ed2L, 0x4c240edc20ec4f9bL, 0xb8a8683e2e624cffL, 0x1de46c427053b06aL, 0xf4facb4094e54479L, 0xf2647723b8fd7d66L, 0x30ffffffceL, 0xffffffffffffffffL, 0xffffffcf00000000L, 0x31L};
uint64_t A[8] = {0x1194785fc0ebd864L, 0xae08dba305d1c30L, 0x637a496883bf13e0L, 0x1e59d7ad07931b9L, 0xfe138e7c3a8da79fL, 0xfaa2ea66baccab45L, 0x46610f593244345L, 0x990198536bb2cc87L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x3b976f3b8380f498L, 0xb4d15ea007b7e3b5L, 0x4de9b5d4419049b1L, 0x149a99810684617L, 0x40afe1ef1031cd4bL, 0x182c0c05668943d1L, 0xa26a2bbd366c9b6eL, 0x3e68dd7af65b8db7L, 0xd0cde987e30aedb6L, 0x2b140a33b5e11040L, 0x85e926ad61547f07L, 0x31828e371390bf98L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 199;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x48344772c13b51a5L, 0x4bf8972de9477b2dL, 0x6d85d4c2d6f573a1L, 0x2d13bcb89e882b91L, 0xd03ec6c99660bf29L, 0x31b19b84173c63ceL, 0x7e91537be5f1636eL, 0x79b022122c12488eL, 0x2058ffffdfa6L, 0xffffffffffffffffL, 0xffffdfa700000000L, 0x2059L};
uint64_t A[8] = {0xe7f5ba6f2554f427L, 0xdf48518b3901ff96L, 0xa828c36c1d4e879bL, 0xef6c4ca1424432edL, 0xedc19f099a5676dfL, 0x8bf2891468410bffL, 0x27cf306a14944795L, 0xb6efb4cd4463768L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcefa3b54b549be6fL, 0x8e63e9626159a555L, 0x6805598f9f4740b4L, 0x1cde7a359e273682L, 0x14f3d99f6fa072b3L, 0x8060d61769c498a3L, 0x586e391f31a46813L, 0x4da200ba40ef744fL, 0x41723e07ee2ec658L, 0x2fba26bca848004L, 0xf96c38831423530bL, 0x2cbe3b93a33c75fL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 200;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xec48700e1ea94049L, 0xe0fd6bf6afa1e383L, 0xf7c889cfa30a0cabL, 0x868f33641354fce3L, 0xb6af50a39cbfb60eL, 0xdecae68017bbb61aL, 0x228a33febb1b22e5L, 0xb539f4b96628d162L, 0xb8747c423ade0ca4L, 0xfffffffff35288e7L, 0x3ade0ca500000000L, 0xcad7718c521f35bL};
uint64_t A[8] = {0x3355a9e2ed6f3d70L, 0xbb8ca626fa2e83a3L, 0x7633a743c1abf15fL, 0x62f6040fe8d14b9aL, 0x5482d45c245c0ed3L, 0xae880bfb66d033f9L, 0x15ecac2d10544c31L, 0xda782cbf9fd78f6dL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x5b627fd416f347d0L, 0x9862152928e44beL, 0x86ee6b49a7eb230cL, 0x110a8b8eb5633573L, 0x44a60348e6e2f306L, 0x4bce2a45e3962b87L, 0xff823506624764d0L, 0x31e4765d592065a4L, 0xa71b06ede75b68f2L, 0x68471acad547b28bL, 0x9c8182a423c13983L, 0xdb14a2ff5bd1090cL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 201;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xea7cc653bf422156L, 0x5fa2a358406937c7L, 0xa7e7ef021f6ef4f8L, 0x76532de45068af2cL, 0x7c1447ce6ec43626L, 0x1371ac2f71e5fda4L, 0x9ba359374a0360a4L, 0xfb9e4785a983d068L, 0xfffffffeffL, 0xffffffffffffffffL, 0xffffff0000000000L, 0x100L};
uint64_t A[8] = {0xadfeeb8858cee75fL, 0xb39892a238929f1eL, 0xd5a7b62826fe4135L, 0xf19b7e5353944d6aL, 0x7d6929a823d46fd1L, 0x821afc9c9cdfd923L, 0xb00c038dd1f7bbf8L, 0xa1625858237504b2L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x187e1ad078f51811L, 0xb763982c7a771f84L, 0xaf965417dc0f6513L, 0x4d9fc9f678c8289cL, 0x2bf400abcb53db37L, 0xa38c059b29fe9af9L, 0xfcf2b2ae5dbbafdaL, 0xa8d795052d1ef760L, 0xc4079291ce44431L, 0xff953a5eb59de00eL, 0x3f89fe20c6fca308L, 0x25affd01fed201L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 202;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xc2cbe95d4366db7aL, 0x4b9eea59999af305L, 0x27894fdaafc25147L, 0xdc05253564ac3744L, 0xf65916d5c27a0714L, 0xe905b4ce8789318eL, 0x6484b48fcdef88cL, 0x8ec05153cb978dcL, 0x2effffffd0L, 0xffffffffffffffffL, 0xffffffd100000000L, 0x2fL};
uint64_t A[8] = {0xfe9ef0ba0cc4d4L, 0xf2ce50c53403e761L, 0x3840a9e7a9b65f5dL, 0x929ccb9306859ad6L, 0xd7c9ea848c225f0cL, 0xc2c3e0c892683433L, 0x17b15172c1bc94f1L, 0x2eb749110972e929L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xcd003c75b05e3e73L, 0x211ef04726e43cf2L, 0xe75e809771785654L, 0xf179db93f8d86fdfL, 0xbcccfd1c79869a3eL, 0xfccd80ec56591489L, 0x7b7ecacc98b79ad1L, 0x38786242c1aa9177L, 0x9c3dc81dc0a48a31L, 0x24da12ff07c86f5aL, 0x76b4bd500d116205L, 0x8eb37ba486f7e77dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 203;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xea227e8207daf84L, 0xd0a68a04691facb3L, 0x42eae592689fa6dfL, 0xc5a5690c083bb0beL, 0xe09b01d2b01a494aL, 0xa0d38dccf62fb3fcL, 0xdd3ff0c9e5d892b1L, 0xe2c87b41f4482659L, 0x1fffffffdfL, 0xffffffffffffffffL, 0xffffffe000000000L, 0x20L};
uint64_t A[8] = {0x9327b0e9666b1242L, 0xf5f3ebfb4d392c57L, 0x7304174a87d08095L, 0x6869c3bcf7e94bb7L, 0xc3c5a8ebeeb43c51L, 0x3ce9943ebc307220L, 0x8fe1ecf0cfcb6406L, 0x710e6e6b5594a88L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x160e2bc7b677a2c4L, 0xfb5de902c3da4fc6L, 0x2f00e21a6dc0cf53L, 0x10ef622fe17d5ab0L, 0x9e7d4af709367470L, 0xe579cc016526f2baL, 0x4782b2dfab709553L, 0x9aeaa01f7672347eL, 0x42fffc3796b40cdL, 0xe12c660f72362319L, 0xae4848092c55d83cL, 0x2d315a739e65b1d2L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 204;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x382006612195ef9bL, 0x74341ea788590c0eL, 0xa3823573e8e04180L, 0xe9966c6cd941560dL, 0xf27760444afa64e5L, 0x4f531742f4373582L, 0xe7b82e4907417307L, 0x1ad7eaffc7b6874bL, 0xba88f35e3cb7f421L, 0xfffffffff740e780L, 0x3cb7f42200000000L, 0x8bf187fc3480bdeL};
uint64_t A[8] = {0x75b1deedf1dd81cdL, 0xcdedb3ab8dbc1d6aL, 0x6dbc4191c033ef74L, 0x99e398a2a8ab239eL, 0xd3e74166fb4fadeeL, 0x2bc2d83bc7d27b02L, 0xae7a6c8895365a36L, 0x163852f12b5f7327L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x82841bbb91c7118aL, 0x3b33433ce3b366dL, 0x5a4e7a8618eabe30L, 0x4af48eea9c60f60bL, 0x362fc6ea8db3d6c3L, 0xe42155545510a807L, 0x4318b62a126b1bfL, 0xe71dd8d55c885133L, 0xfbcfca1afeb3224L, 0x4f6df9e64c9bb3d6L, 0xa401d300093d9db0L, 0x39f918b386cd9b78L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 205;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x62e71f02310d6738L, 0x958e3fa1590d4343L, 0x1b1203ab1aa865f2L, 0xc2964235d86c997L, 0x5ea360fdd4207f1dL, 0xffeae33369aa1b42L, 0x521599dbc2762191L, 0xbc7292db823be8a2L, 0x745effff8ba0L, 0xffffffffffffffffL, 0xffff8ba100000000L, 0x745fL};
uint64_t A[8] = {0x4456267a778d8ce7L, 0x505993680c1898cbL, 0x55922df39fbd224eL, 0xc0180d950146ecc4L, 0xdeb795728c6f4f34L, 0x57faade95e5c0b30L, 0x59e264b4ada4bf27L, 0xb77fdb881e63a97cL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xc37c10c3c78f981eL, 0x1372f863ddf9ca14L, 0x39e772d3159aef6cL, 0xac44a798caefeb00L, 0xaee5a684592b873L, 0xdcb127e1b102fcb4L, 0xffa8abd7f34ba95aL, 0xc7f057c79a53613dL, 0x3f47a3a4ea48e5fdL, 0x57df931e052767bbL, 0x502f2f17fb36a952L, 0x351fc4d64624a811L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 206;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x5bb15448e44ae6a3L, 0x962a79c74619f5bcL, 0x930911d215edec05L, 0x7902957dfcfcd34bL, 0xc4949acb3e6dee02L, 0xe90482c9ede219c0L, 0xbeae72a4d500537L, 0x92a95e8c08c9aef4L, 0x1cb8e0ffe346dd3dL, 0xffffffffffffbe3dL, 0xe346dd3e00000000L, 0x41c21cb922c2L};
uint64_t A[8] = {0x57fcaf64b5e8d6dbL, 0xf670e79ac97efbdcL, 0xe12253fbdb991b94L, 0xa928a6d84768c868L, 0x1d94d6153c3e2656L, 0x2085b6e8694a3819L, 0xea05005e197a2805L, 0x8004d784b244753L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xb6535c637643c3b4L, 0x26452eb6846cf532L, 0xea5bb0ebaa99ebcbL, 0x909f0298e16ad692L, 0x16b53624f4a87f72L, 0x89a742299ac73e8L, 0xc1f0d4cea8e0ffd1L, 0xa484f5a8e59f5c36L, 0x86add1054dc07c8dL, 0xf9eba42054189b4dL, 0xe9ebc2a3aeec4a24L, 0xe8477646ce2dff2dL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 207;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x93b61fff461c0193L, 0x245b6a631620a3L, 0x980d7cfd6373e432L, 0xdb3228555a066f55L, 0x2fa41654b02a0c20L, 0x6a9156a5d8a0365bL, 0xfeeba3cfa8da8148L, 0xb8a90345d2bf3fbfL, 0x894fffff76aL, 0xffffffffffffffffL, 0xfffff76b00000000L, 0x895L};
uint64_t A[8] = {0xb5cffedf0790a013L, 0xf1ba0f6e25458e39L, 0x66d546ad56e03b9bL, 0x7ce0061255f79ecfL, 0x7c2da8ba0847c739L, 0xc641e310a7eb8838L, 0xf3cc871d693e2a73L, 0x16439c6cd3b5b4e4L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xe65a73ef42d3afc7L, 0x66042e6ed3abf3feL, 0x7bc7124250947decL, 0x4ff9991acde231b0L, 0x65342915b9c7e648L, 0x94fe48a8eba8523dL, 0xc3b8b6d4900027f4L, 0x907dd33f7e1f94d8L, 0x48c4dea9de69ae8cL, 0x1a814d1fe0590615L, 0x1d8216a88d702430L, 0xda7c9f873a086808L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 208;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xcbceda9779a886deL, 0x3fe90d812619b86bL, 0x4159848c383b7cefL, 0xcba63eab99fdaf73L, 0x3573c4a4d803ba9eL, 0x9db6fde5ab35d99dL, 0x15f2104c4e6e005cL, 0x7fb503ed5185c70bL, 0xe4762cda1b6b0c32L, 0xffffffffffe1390dL, 0x1b6b0c3300000000L, 0x1ec6f2e494f3cdL};
uint64_t A[8] = {0x81d4d67d5303aa9L, 0x55d6984e2ed8d949L, 0x9ea7ce6365f0934aL, 0x69b60cd9343b297aL, 0xa916a98dc09558fbL, 0x4a43bfd951bdba86L, 0x6c7cc30329ddb815L, 0xd6b16ee90d413600L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0xef5a86ba12b10f51L, 0xa14232c6c2094dbeL, 0xa041a36456bcffbaL, 0x79bceb0a418ceee3L, 0xe1b0d5a052d6d440L, 0x747bfacc02ebc51cL, 0xf885a4c48866b187L, 0xa02d93fa05651a88L, 0xa1fac4c43b84d98fL, 0x1fe958debe7aaccdL, 0xbd334d839f8fc0abL, 0xfd5de16b7a97131L};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 209;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xa8b9dc95740882cfL, 0x9ec81ffe5b603bdeL, 0x98e8135f66721b56L, 0xd17ff993343047c3L, 0xd5486ac6f39da9f8L, 0xa97b7def431b4400L, 0x359aaacee9bc1ac2L, 0xd27547a73ca8ecc9L, 0xa352943f5cad6bbcL, 0xfffffffffffffffcL, 0x5cad6bbd00000000L, 0x3a3529443L};
uint64_t A[8] = {0x9aa4819ec5eb4a3L, 0x843d527627103033L, 0x4fb6be2872eb797bL, 0x63408a083be2d806L, 0x2df5acb69dffcb33L, 0x7a7d39ea8034a362L, 0x63895b730257c52dL, 0x6f93d9ef8f89e6bbL};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x1259843f1f79324bL, 0x8c4109a33190bddeL, 0xbea9029b3905f178L, 0xe4cbc7d6def1e497L, 0x280e2a2a86b41127L, 0x2689fc9b3c330270L, 0x9a66377d92ce4006L, 0x3da5c4e43d4b5fdfL, 0x21c382adcbfacadaL, 0x4ba570ff44e6e39dL, 0xfc7d46696884f8bL, 0x9eca9586b4e358edL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 210;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0xf6473dfddab6bf9L, 0x890c51b091c17925L, 0x3af4337690955505L, 0x9391e981ecee3f12L, 0xcbcf4be60e230b39L, 0x514815022786fe34L, 0x32ce1b903bfb4a5cL, 0x564202ccfa508237L, 0x49ffffffb5L, 0xffffffffffffffffL, 0xffffffb600000000L, 0x4aL};
uint64_t A[8] = {0x1ac9b3b95c98837aL, 0x8d80cea9a6380e97L, 0x68b05abd2b4c70a9L, 0x1297113175774cf6L, 0xf9b38f9d5ef51755L, 0x5566e3f4088317ddL, 0x279b1cdeee4dfc85L, 0x58aecf8f412543b5L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x7ad2fff36c3b2e26L, 0xb2f3bc5c23d87ac9L, 0x3765769e4524ff25L, 0x23665cd85fd6eaf2L, 0x1a31624bf8be29dfL, 0x3cd8e7dee97a44c2L, 0x33eb4b4006c4eb0eL, 0x3b616dc4d9e5d7a2L, 0x4865811a5328a1c2L, 0x9c480de2eb0bdd65L, 0xa5f7b71dd250567dL, 0xbcf9b92b34d85d5aL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 211;
}
{
uint64_t out[12] = {0};
uint64_t J[12] = {0x9f8aa54b2ef7c76aL, 0x49d2c9eb084ffdd7L, 0xd36a42d7aebf7313L, 0x42c2af497e2feb4L, 0x2d431068d84bde31L, 0x2d97d10878eb4cbbL, 0x3bd0c66fddb7fb58L, 0x9200b7ba09895e70L, 0xfffffffeL, 0xffffffffffffffffL, 0xffffffff00000000L, 0x1L};
uint64_t A[8] = {0x54d66b2b865ea511L, 0xf978c0d61d3d25bcL, 0xf8de9aeb66f71bb1L, 0xb5ab5f4ce49972d0L, 0xc04e122cb67e556aL, 0xaab1e105c967237cL, 0x4a21fe89db473987L, 0xaabbba599d15ce42L};
// both nz
p256_jacobian_add_affine(out, J, A);
uint64_t ref[12] = {0x5da7b46e081a80f7L, 0x9f2d1cc77e706bf5L, 0xd44a1379be3d42abL, 0xdf07f82afa2f5227L, 0x9f7851a3ecb06593L, 0xc35891dab8b63c63L, 0x2bd457cf2e2ac8b1L, 0xd00265a18454fceL, 0xb54bc5df5766dda8L, 0xafa5f6eb14ed27e5L, 0x25745814b837a89eL, 0xb17f34584cb6741bL};
if (memcmp(out, ref, sizeof(uint64_t)*12)) return 212;
}

return 0;
}
