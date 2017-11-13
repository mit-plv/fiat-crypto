#!/bin/bash

for impldir in src/Specific/*32_*2e* ; do
	
	sh -c "arm-linux-androideabi-gcc -pie \
		$(tail -1 "$impldir/compiler.sh" | tr ' ' '\n' | grep -A99999 -- -D  | grep -v '"$@"' | tr '\n' ' ') \
		-I \"$impldir\" \
		-std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing \
		src/Specific/Framework/bench/fibe.c \
		-o /tmp/main" \
		> /dev/null 2> /dev/null \
		&& printf "%s\tfibe\n" "$(basename "$impldir")" && adb push /tmp/main /data/local/tmp/main >/dev/null 2>/dev/null && adb shell "time /data/local/tmp/main" || continue
	
	sh -c "arm-linux-androideabi-gcc -pie \
		$(tail -1 "$impldir/compiler.sh" | tr ' ' '\n' | grep -A99999 -- -D  | grep -v '"$@"' | tr '\n' ' ') \
		-I \"$impldir\" \
		-I ~/android-toolchain/gmp-6.1.2/ \
		-std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing \
		src/Specific/Framework/bench/gmpvar.c \
		$HOME/android-toolchain/gmp-6.1.2/.libs/libgmp.a \
		-o /tmp/main" \
		> /dev/null 2> /dev/null \
		&& printf "%s\tgmpvar\n" "$(basename "$impldir")" && adb push /tmp/main /data/local/tmp/main >/dev/null 2>/dev/null && adb shell "time /data/local/tmp/main"
	
	sh -c "arm-linux-androideabi-gcc -pie \
		$(tail -1 "$impldir/compiler.sh" | tr ' ' '\n' | grep -A99999 -- -D  | grep -v '"$@"' | tr '\n' ' ') \
		-I \"$impldir\" \
		-I ~/android-toolchain/gmp-6.1.2/ \
		-std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing \
		src/Specific/Framework/bench/gmpsec.c \
		$HOME/android-toolchain/gmp-6.1.2/.libs/libgmp.a \
		-o /tmp/main" \
		> /dev/null 2> /dev/null \
		&& printf "%s\tgmpsec\n" "$(basename "$impldir")" && adb push /tmp/main /data/local/tmp/main >/dev/null 2>/dev/null && adb shell "time /data/local/tmp/main"

	# fails to find libc++ on android
	# 
	# sh -c "arm-linux-androideabi-g++ -pie \
	# 	$(tail -1 "$impldir/compiler.sh" | tr ' ' '\n' | grep -A99999 -- -D  | grep -v '"$@"' | tr '\n' ' ') \
	# 	-I \"$impldir\" \
	# 	-I ~/android-toolchain/gmp-6.1.2/ \
	# 	-L /usr/lib/android-ndk/sources/cxx-stl/llvm-libc++/libs/armeabi/ \
	# 	-Wl,--allow-multiple-definition \
	# 	-std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing \
	# 	src/Specific/Framework/bench/gmpxx.cpp \
	# 	$HOME/android-toolchain/gmp-6.1.2/.libs/libgmp.a \
	# 	-o /tmp/main" \
	# 	&& printf "%s\tgmpxx\n" "$(basename "$impldir")" && adb push /tmp/main /data/local/tmp/main >/dev/null 2>/dev/null && adb shell "time /data/local/tmp/main"
	printf "\n"
done
