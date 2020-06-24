FROM ubuntu:16.04
MAINTAINER Yizhuo Zhai <yizh.zhai@gmail.com>
WORKDIR /home/UBITect
COPY . /home/UBITect

RUN apt-get update -y && \
    apt-get install -y build-essential curl libcap-dev git cmake libncurses5-dev python-minimal python-pip unzip libtcmalloc-minimal4 && \
    apt-get install -y zlib1g-dev libgoogle-perftools-dev && \
    DEBIAN_FRONTEND=noninteractive apt -y --no-install-recommends install sudo emacs-nox vim-nox file python3-dateutil && \
    cd llvm && \
    mv llvm.src/projects/BBTag/ . && \
    ./build-llvm.sh && \
    export LLVM_SRC=/home/UBITect/llvm/llvm.src && \
    export LLVM_DIR=/home/UBITect/llvm/build && \
    export PATH=$LLVM_DIR/bin:$PATH && \
    echo $PWD && \
    mv BBTag llvm.src/projects && \
    cd build &&\
    rm CMakeCache.txt && \
    cmake -G "Unix Makefiles" -DLLVM_ENABLE_RTTI=ON -DCMAKE_BUILD_TYPE=Debug ../llvm.src &&\
    make && \
    cd ../.. && \
    make && \
    cd KLEE/z3 && \
    python scripts/mk_make.py && \
    cd build && \
    make && \
    make install && \
    cd ../../klee && \
    mkdir build && \
    cd build && \
    cmake -DENABLE_SOLVER_Z3=ON -DENABLE_UNIT_TESTS=OFF -DENABLE_SYSTEM_TESTS=OFF -DLLVM_CONFIG_BINARY=../../../llvm/build/bin/llvm-config -DLLVMCC=../../../llvm/build/bin/clang -DLLVMCXX=../../../llvm/build/bin/clang++  .. && \
    make  && \
    pip install psutil

COPY . .
