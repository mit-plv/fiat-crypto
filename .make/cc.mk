# © 2012–2015 the Massachusetts Institute of Technology
# @author bbaren

CC = clang
CXX = clang++

CPPFLAGS = \
	-Wall \
	-D_FORTIFY_SOURCE=2

CXXFLAGS = \
	-std=c++11 \
	-ftrapv \
	-fstack-protector-strong --param=ssp-buffer-size=4 \
	-fPIC \
	-O2 -g \
	-ffunction-sections -fdata-sections \
	-Weverything -Wno-c++98-compat

LDFLAGS = -fPIE -pie
