#!/bin/bash -e

CUR_DIR=$PWD

if [ ! -d "build" ]; then
  mkdir build
fi

cd build
cmake -G "Unix Makefiles" -DLLVM_ENABLE_RTTI=ON -DCMAKE_BUILD_TYPE=Release ../llvm.src
make

#if [ ! -d "$CUR_DIR/prefix" ]; then
#  mkdir $CUR_DIR/prefix
#fi

#cmake -DCMAKE_INSTALL_PREFIX=$CUR_DIR/prefix -P cmake_install.cmake

