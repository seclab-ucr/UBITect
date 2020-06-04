# UBITect: A Precise and Scalable Method to Detect Use-Before-Initialization Bugs in Linux Kernel
Authors: Yizhuo Zhai, Yu Hao, Hang Zhang, Daimeng Wang, Chengyu Song, Zhiyun Qian, Mohsen Lesani, Srikanth V. Krishnamurthy, Paul Yu

UBITect is a UBI bug finding tool which combines flow-sensitive type qualifier analysis and symbolic execution to perform precise and scalable UBI bug detection. This repo is our implementation, we conducted our experiment on ubnuntu 16.04, if there's any problem for the experiment, please contact the following author:
```
Yizhuo Zhai
Department of Computer Science and Engineering
University of California, Riverside
yzhai003@ucr.edu
```
## Files
|  
|-src: Qualifier Inference code for UBITect  \
|-KLEE: Under constraint symbolic execution code and z3 as the contraint solver  \
|-llvm: The source code for llvm, clang and the tag pass  \
|-example: An example showcase how UBITect works in below  \
|-Makefile: Used to compile qualifier inference code in src/  \
|-path_verify.py: Wrapper to run KLEE 
## How to use UBITect:
```sh
    #change to the code folder
    $cd UBITect
    #build LLVM used
    $cd llvm.src
    $./build-llvm.sh
    #build the UBITect
    $cd ../../
    $make
	
```
Build the bitcode file with -O0 optimization and -g option, then tag it:
```sh
    $opt -load dir/to/llvm/build/lib/bbTaglib.so -bbtag bitcode-before-tag >>bitcode-after-tag
```
Use UBITect to generate the potential warnings:
```sh
    # To analyze a single bitcode file, say "test.bc", run:
    $./build/ubitect -ubi-analysis test.bc 
    # To analyze a list of bitcode files, put the absolute paths of the bitcode files in a file, say "bc.list", then run:
    $./build/ubitect -ubi-analysis @bc.list
```
The initial warnings are showed in terminal in format [[code] cfile: line in tested code (.c file)], we assume the test.c is compiled to test.bc
Also, the warnings with guidance is put in ```warnings.json```

Use under-constrained symbolic execution to verify the result:
```sh
    #Install dependencies:
    $sudo apt-get install build-essential curl libcap-dev git cmake libncurses5-dev python-minimal python-pip unzip libtcmalloc-minimal4 libgoogle-perftools-devz lib1g-dev
    #Install constraint solver under UBITect/:
    $cd KLEE
    $./build-klee.sh
```

Now the ready-to use klee is cur/path/2018_klee_confirm_path/build/bin/klee
Add the absolute path of klee to path_verify.py
```sh
    $vi path_verify.py
```
```python
    klee_path="Dir/To/klee"

```
```
    $wq
    #run klee via the wrapper, the default time limit is 120s and memory limit is 2GB if
    $./path_verify.py warnings.json 
    #if you want to define the time limit(s) and memory limit(GB), e.g., 10s and 1 GB, run
    $./path_verify.py warnings.json 10 1
```
Now the verified results are showed in the confirm_result.json in the current directory
# Example
An example is put under subdirectory example/
```sh
$cd example/
```
backlog.c is a piece of vulnerable code simplified from [linux commit 1a92b2b](https://github.com/torvalds/linux/commit/1a92b2ba339221a4afee43adf125fcc9a41353f7),
the variable **backlog** could be uninitialized if **a** is zero. Then this pointer is used in line 25 (if statement) and line 26 (dereferenced). The following
steps show how UBITect detects them.
```c
#include <stdio.h>

enum engine_status {
        ENGINE_IDLE,
        ENGINE_BUSY,
        ENGINE_W_DEQUEUE,
};
struct test_struct{
        int irq;
        enum engine_status eng_st;
};
struct aStruct{
        enum engine_status eng_st;
};
struct test_struct *init;
struct aStruct *cpg;
int test(int a){
        struct test_struct *backlog;
        cpg->eng_st = ENGINE_BUSY;

        if (a){
                backlog = init;
        }

        if(backlog){ /*line 25*/
                backlog->irq = 0; /*line 26*/
                cpg->eng_st = ENGINE_IDLE;
        }
        return 0;
}
```
```sh
#Compile it to bitcode file and tag the basic block:
$clang -emit-llvm -O0 -g -c backlog.c -o backlog.llbc
#tag the basic block:
$opt -load ../llvm/build/lib/bbTaglib.so -bbtag backlog.llbc >>backlog.bc
#Apply UBITect on tagged bitcode file:
$./../build/ubitect -ubi-analysis absolute/path/to/backlog.bc
```
Two warning is showed in the terminal, indicating the potential uninitialized use
```sh
 [[Code] backlog.c: +25]
 [[Code] backlog.c: +26]

```
The warnings with guidance are put inside warnigs.json under current directory which aids the under-constraint symbolic execution to verify the result.
```json
absolute/path/to/UBITect/example/backlog.bc:
{
"blacklist": ["backlog.llbc-test-1", "backlog.llbc-test-3", "backlog.llbc-test-4"], 
"use": "backlog.llbc-test-2", "warning": "  %3 = load %struct.test_struct*, %struct.test_struct** %backlog, align 8, !dbg !46", 
"whitelist": ["backlog.llbc-test-0"]}
......
}
```
Main fields guiding the klee to explore the feasible path:
```
-blacklist: LLVM basic blocks that klee should avoid when explore the feasible path, in this example, blacklist contains "backlog.llbc-test-1", from the control flow graph showed below, this basic block will initialize backlog, to trigger the bug, this basic block should not in our path. "backlog.llbc-test-3" and "backlog.llbc-test-4" is in the blacklist because they cannot reach the use, therefore, we can make klee stop earlier.
-whitelist: LLVM basic blocks that the feasible path must include, in this example, we have "backlog.llbc-test-0", because it's the definition of the backlog, therefore, this basic block must in the path.
-use: The basic block where the uninitialzied use happens, also the end block when klee explore the path, this warning is reported in "if(backlog)", which happens in "backlog.llbc-test-2"
```
LLVM control flow graoh looks like:
```llvm
+----------------------------------------------------------------------------------+
|backlog.llbc-test-0:                                                              |
|  %a.addr = alloca i32, align 4                                                   |
|  /*struct test_struct *backlog;*/                                                |
|  %backlog = alloca %struct.test_struct*, align 8                                 |
|   ......                                                                         |
| /*if(a)*/                                                                        |
| %tobool = icmp ne i32 %1, 0, !dbg !39     [if(a)]                                |
|  br i1 %tobool, label %backlog.llbc-test-1, label %backlog.llbc-test-2, !dbg !41 |-----------+
+----------------------------------------------------------------------------------+           |
                                     |                                                         |
                                    \|/                                                        |
+-----------------------------------------------------------------------------------+          |
|backlog.llbc-test-1:                               ; preds = %backlog.llbc-test-0  |          |
|  %2 = load %struct.test_struct*, %struct.test_struct** @init, align 8, !dbg !42   |          |
|  /*[backlog = init;] */                                                           |          |
|  store %struct.test_struct* %2, %struct.test_struct** %backlog, align 8, !dbg !44 |          |
|  br label %backlog.llbc-test-2, !dbg !45                                          |          |
+-----------------------------------------------------------------------------------+          |
                        |                                                                      |
                        |                                                                     \|/
                        |                +-----------------------------------------------------------------------------------+ 
                        |                |backlog.llbc-test-2:                              ; preds = %backlog.llbc-test-1/0 |
                        |                |  %3 = load %struct.test_struct*, %struct.test_struct** %backlog, align 8, !dbg !46| 
                        |                | /*if(backlog)*/                                                                   |
                        |                |  %tobool1 = icmp ne %struct.test_struct* %3, null, !dbg !46                       |
                        |                |  br i1 %tobool1, label %backlog.llbc-test-3, label %backlog.llbc-test-4, !dbg !48 |
                        |                +-----------------------------------------------------------------------------------+ 
                        |                                                                                   |
                       \|/                                                                                  |
+-----------------------------------------------------------------------------------------------------+     |
|backlog.llbc-test-3:                                               ; preds = %backlog.llbc-test-2    |     |
|  %4 = load %struct.test_struct*, %struct.test_struct** %backlog, align 8, !dbg !49                  |     |
|   /*backlog->irq = ...*/                                                                            |     |
|  %irq = getelementptr inbounds %struct.test_struct, %struct.test_struct* %4, i32 0, i32 0, !dbg !51 |     |
|   ......                                                                                            |     |
+-----------------------------------------------------------------------------------------------------+     |
                                                        |                                                   |
                                                       \|/                                                 \|/
                                                +-----------------------------------------------------------------------------+
                                                |backlog.llbc-test-4:    ; preds = %backlog.llbc-test-3, %backlog.llbc-test-2 |
                                                |  ret i32 0, !dbg !57                                                        |
                                                +-----------------------------------------------------------------------------+


```

```sh
#change the klee_path inside ../path_verify.py and then
$cp ../path_verify.py .
$python path_verify.py warnings.json
```
After the path exploration, klee verifies that those are true positives as:
```
[SrcCode] backlog.c +25
[SrcCode] backlog.c +26
```
Meaning the uninitalized use appears in line 25 and line 26, the details are inside confirm_result.json, it adds the related information of the 
feasible path. 
```json
{
"path":["false :   br i1 %tobool, label %backlog.llbc-test-1, label %backlog.llbc-test-2, !dbg !37"],
"input_0":"#x0000000000000000"},
......
}

- path shows the feasible path found by klee: in the first branch, the path goes to the false branch
- input_0: when input is 0 (#x0000000000000000), this path is feasible
```
## Prepare LLVM bitcode files of OS kernels
* The code should be compiled with the built LLVM
* We use the github repo and the wrapper to compile the kernel code
* Please follow the compilation instructions in https://github.com/YizhuoZhai/lll-414.git to get the bitcode files
