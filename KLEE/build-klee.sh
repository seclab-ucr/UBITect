CUR_DIR=$PWD

cd z3
python scripts/mk_make.py --prefix=${CUR_DIR}/z3/prefix
if [ ! -d "build" ]; then
          mkdir build
fi
cd build
make
make install

export Z3PATH=${CUR_DIR}/z3/prefix
export Z3_INCLUDE_DIRS=${CUR_DIR}/z3/build/include


cd ../../klee
if [ ! -d "build" ]; then
          mkdir build
fi
mkdir build
cd build
cmake -DENABLE_UNIT_TESTS=OFF -DENABLE_SYSTEM_TESTS=OFF ..
make -j4

export PATH="$LLVM_DIR/bin:$Z3PATH/bin:$HOME/bin:$HOME/.local/bin:$PATH"
