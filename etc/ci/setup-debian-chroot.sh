#/bin/sh
set -e -u -x
debian="$1"

# This script is intended to be called from github hosted runners only.
# It does not clean up after itself.

sudo mkdir /chroot
sudo apt-get -q -y -o Acquire::Retries=30 update
sudo apt-get -q -y -o Acquire::Retries=30 install debootstrap
sudo debootstrap --variant=minbase "$debian" /chroot http://debian-archive.trafficmanager.net/debian/ || ( cat /tmp/tmp.*/debootstrap/debootstrap.log ; exit 1 )
sudo mount proc /chroot/proc -t proc
sudo mount sysfs /chroot/sys -t sysfs
sudo chroot /chroot apt-get -q -y -o Acquire::Retries=30 install sudo git make time jq python3 python-is-python3 ocaml coq libcoq-core-ocaml-dev libfindlib-ocaml-dev ocaml-findlib cabal-install
sudo chroot /chroot groupadd -g "$(id -g)" "$(id -g -n)"
sudo chroot /chroot useradd  -g "$(id -g)" -u "$(id -u)" "$(id -u -n)"
printf "%s ALL=(ALL) NOPASSWD: ALL\n" "$(id -u -n)" | sudo tee /chroot/etc/sudoers.d/root
sudo mkdir -p "/chroot/$HOME"
sudo chown "$(id -u):$(id -g)" "/chroot/$HOME"
sudo mount --bind "$HOME" "/chroot/$HOME"

( cd "$(dirname "$0")" && pwd ) | tee -a "$GITHUB_PATH"
