## Running RISC-V programs compiled with the bedrock2 compiler in qemu user mode using system calls of the host OS

### Prerequisites

1) A RISC-V assembler & linker. On a Fedora Linux, I got it by installing all of the GNU RISC-V toolchain (but maybe there are more lightweight ways).

```
sudo dnf install autoconf automake python3 libmpc-devel mpfr-devel gmp-devel gawk  bison flex texinfo patchutils gcc gcc-c++ zlib-devel expat-devel
mkdir /home/sam/installs/riscv-gnu-toolchain32/
git clone --recursive git@github.com:riscv/riscv-gnu-toolchain.git
cd ./riscv-gnu-toolchain
./configure --prefix=/home/sam/installs/riscv-gnu-toolchain32 --with-arch=rv32ima --with-abi=ilp32
make linux
cd ~/installs/riscv-gnu-toolchain32/bin/
export PATH=`pwd`:$PATH
```

2) qemu user mode emulator

```
sudo dnf install qemu-user
```


### Compiling & running

Create a Coq file that outputs a hex dump of encoded instructions (eg `CompilerTest.v`), then run eg

```
make CompilerTest.exe
qemu-riscv32 CompilerTest.exe
```

and use `echo $?` to check the exit code.
