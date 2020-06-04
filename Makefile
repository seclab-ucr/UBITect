CUR_DIR = $(shell pwd)
LLVM_SRC := ${CUR_DIR}/llvm/llvm.src
LLVM_BUILD := ${CUR_DIR}/llvm/build
UBITECT_DIR := ${CURDIR}/src
UBITECT_BUILD := ${CURDIR}/build

build_ubitect_func = \
    (mkdir -p ${2} \
        && cd ${2} \
        && PATH=${LLVM_BUILD}/bin:${PATH} \
            LLVM_ROOT_DIR=${LLVM_BUILD}/bin \
            LLVM_LIBRARY_DIRS=${LLVM_BUILD}/lib \
            LLVM_INCLUDE_DIRS=${LLVM_BUILD}/include \
            CC=clang  CXX=clang++ \
            cmake ${1} -DCMAKE_BUILD_TYPE=Release \
                -DCMAKE_CXX_FLAGS_RELEASE="-std=c++1y -frtti -fpic" \
        && make -j${NPROC})

all: ubitect

ubitect:
	$(call build_ubitect_func, ${UBITECT_DIR}, ${UBITECT_BUILD})
