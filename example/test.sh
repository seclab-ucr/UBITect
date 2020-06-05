#!/bin/bash -e

CUR_DIR=$PWD

#Compile it to bitcode file and rename the basic block:
../llvm/build/bin/clang -emit-llvm -O0 -g -fno-short-wchar -c backlog.c -o backlog.llbc
#tag the basic block:
../llvm/build/bin/opt -load ../llvm/build/lib/bbTaglib.so -bbtag backlog.llbc >>backlog.bc
#Apply UBITect on tagged bitcode file:
./../build/ubitect -ubi-analysis ${CUR_DIR}/backlog.bc

