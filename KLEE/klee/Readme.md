# Need

`llvm-7`

`clang-7`

# Install dependencies
```
sudo apt-get install build-essential curl libcap-dev git cmake libncurses5-dev python-minimal python-pip unzip libtcmalloc-minimal4 libgoogle-perftools-devz lib1g-dev

```

# Install constraint solver
```
git clone git@github.com:Z3Prover/z3.git
cd z3
python scripts/mk_make.py
cd build
make
sudo make install
```

# Build
```
git clone git@github.com:ZHYfeng/2018_klee_confirm_path.git
cd 2018_klee_confirm_path
mkdir build
cd buikd
cmake -DENABLE_UNIT_TESTS=OFF -DENABLE_SYSTEM_TESTS=OFF ..
make -j4
sudo make install
```

# Use
```
klee -entry-point=ping_get_first -white-list=./white-list -black-list=./black-list -use-list=./use-list ./ping.bc
```

+ `ping_get_first` is function name.
+ `./white-list` is path of white list file.
+ `./black-list` is path of black list file.
+ `./use-list` is path of use list file.
+ `./ping.bc` is the path of bc file.
+ It maybe need name of rusult file.
+ It now can run with the two case you give me. Let me know what errors with other case.