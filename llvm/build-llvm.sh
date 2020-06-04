#!/bin/bash -e

CUR_DIR=$PWD

if [ ! -d "build" ]; then
  mkdir build
fi

cd build
cmake -DLLVM_TARGET_ARCH="X86;AArch64" -DLLVM_TARGETS_TO_BUILD="X86;AArch64" -DLLVM_ENABLE_RTTI=ON -DCMAKE_BUILD_TYPE=Debug ../llvm.src
make -j8

if [ ! -d "$CUR_DIR/prefix" ]; then
  mkdir $CUR_DIR/prefix
fi

cmake -DCMAKE_INSTALL_PREFIX=$CUR_DIR/prefix -P cmake_install.cmake

export LLVM_BUILD=${CUR_DIR}/prefix
export PATH=$LLVM_BUILD/bin:$PATH
