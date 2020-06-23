# UBITect: A Precise and Scalable Method to Detect Use-Before-Initialization Bugs in Linux Kernel

Authors: Yizhuo Zhai, Yu Hao, Hang Zhang, Daimeng Wang, Chengyu Song, Zhiyun Qian, Mohsen Lesani, Srikanth V. Krishnamurthy, Paul Yu

UBITect is a UBI bug finding tool which combines flow-sensitive type qualifier analysis and symbolic execution to perform precise and scalable UBI bug detection. For more details, please refer to our paper. This repo is our implementation, we conducted our experiment on machines with Intel(R) Xeon(R) E5-2695v4 processors and 256GB RAM. The operating system is the 64 bit Ubuntu 16.04 LTS. Please contact the following author for any questions:
```
Yizhuo Zhai
Department of Computer Science and Engineering
University of California, Riverside
yzhai003 at ucr dot edu
```
## Files
|  
|-src: Qualifier Inference code for UBITect  \
|-KLEE: Under constraint symbolic execution code and z3 as the contraint solver  \
|-llvm: The source code for llvm, clang and the basic block rename pass\*, we use llvm-7.0.0 and clang 7.0.0  \
|-example: An example showcase how UBITect works in below  \
|-Makefile: Used to compile qualifier inference code in src/  \
|-path_verify.py: Wrapper to run KLEE \
|-getbclist.py: A wrapper to rename the basic block and collect the LLVM bitcode files for OS kernels \
|-Dockerfile: The Dockerfile to install the tool with Docker 
\* The rename pass is a llvm pass which gives every basic block in the folder an identifier. By default, llvm names the basic block as 1%, 2%, etc, which is hard for human to track.  This pass rename the basic blocks with bitcode name, function name and basic block number for human understandability, the loadable library is called ```bbTaglib.so```, we already use wrappers to integrate the rename process, the users do not need to care about it now.

## Installation:
### Installation with cmake
```sh
    #change to the code folder
    $cd UBITect
    #build LLVM
    $cd llvm
    $./build-llvm.sh
    #build the qualifer inference
    $cd ..
    $make
    #install the dependencies used by KLEE and z3
    $sudo apt-get install build-essential curl libcap-dev git cmake libncurses5-dev python-minimal python-pip unzip libtcmalloc-minimal4 libgoogle-perftools-dev zlib1g-dev
    #build the KLEE
    $cd KLEE
    $./build-klee.sh
    #install python putils
    $pip install psutil
```
Now the ready to use binaries are path/to/UBITect/build/bin/ubitect and path/to/UBITect/KLEE/klee/build/bin/klee
### Installation with Docker
```sh
    #build with Dockerfile
    $docker build --tag ubitect:1.0 .
    #run docker image
    $docker run -it ubitect:1.0 /bin/bash
``` 

## How to use UBITect
This section shows the essential steps to apply UBITect to the target code, we will have a detailed step by step tutorial with a concrete example in the next section.
* Compile the target code with options: -O0, -g, -fno-short-wchar
* Rename the basic block and generate bitcode.list by the wrapper getbclist.py
```sh
    $python getbclist.py abs/dir/to/llvm
```
Use path/to/UBITect/build/ubitect to generate the potential warnings:
```sh
    # To analyze a single bitcode file, say "test.bc", run:
    $./build/ubitect -ubi-analysis abs/path/to/test.bc 
    # To analyze a list of bitcode files, put the absolute paths of the bitcode files in a file, say "bitcode.list", then run:
    $./build/ubitect -ubi-analysis @bitcode.list
```
The initial warnings are shown in terminal in format [[code] cfile: line in tested code (.c file)], we assume the test.c is compiled to test.bc
Also, the initial warnings with guidance for symbolic execution is put in ```warnings.json```

Use path/to/UBITectKLEE/build/bin/klee to explore feasible paths, add home_path="Dir/To/UBITect" to path_verify.py.
```    
    #run klee via the wrapper, the default time limit is 120s and memory limit is 2GB if
    $python ./path_verify.py warnings.json 
    #if you want to define the time limit(s) and memory limit(GB), e.g., 10s and 1 GB, run
    $python ./path_verify.py warnings.json 10 1
```
Now the results with feasible paths are put in the confirm_result.json in the current directory.
## Step by Step Tutorial
This section uses a simple piece of code to show the workflow of UBITect and explains the intermediate output for readers who are intersted. For readers who care more about how to manually verify the result with the aid of symbolic execution, feel free to run the command, skip the explanation and then read the step 4.
### Step 1: Undersand the example code:
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
### Step 2: Qualifier inference generate the potential uninitilaized use:
```sh
$cd example/
$../llvm/build/bin/clang -emit-llvm -O0 -g -fno-short-wchar -c backlog.c -o backlog.llbc
#If you are running in the Docker, then the abs/dir/to/UBITect/llvm is /home/UBITect/llvm
$python ../getbclist.py abs/dir/to/UBITect/llvm
$../build/ubitect -ubi-analysis @bitcode.list
```
Two warnings appear in the terminal, indicating the potential uninitialized use
```sh
 [[Code] backlog.c: +25]
 [[Code] backlog.c: +26]

```
The warnings with guidance are put inside warnings.json under current directory which aids the under-constraint symbolic execution to explore the feasible path.
```json
absolute/path/to/UBITect/example/backlog.bc:
{
"blacklist": ["backlog.llbc-test-1", "backlog.llbc-test-3", "backlog.llbc-test-4"], 
"use": "backlog.llbc-test-2", "warning": "  %3 = load %struct.test_struct*, %struct.test_struct** %backlog, align 8, !dbg !46", 
......
}
```
Main fields guiding the klee to explore the feasible path:
```
-blacklist: LLVM basic blocks that klee should avoid when explore the feasible path, in this example, blacklist contains "backlog.llbc-test-1", from the control flow graph showed below, this basic block will initialize backlog, to trigger the bug, this basic block should not in our path. "backlog.llbc-test-3" and "backlog.llbc-test-4" is in the blacklist because they cannot reach the use, therefore, we can make klee stop earlier.
-use: The basic block where the uninitialzied use happens, also the end block when klee explore the path, this warning is reported in "if(backlog)", which happens in "backlog.llbc-test-2"
```
For easy reference, we put the LLVM control flow graph here:
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
### Step 3: Use klee to find the feasible path
change the home_path inside ../path_verify.py to path/to/UBITect (If you are running in the Docker, then home_path = "/home/UBITect") and then
```sh
$python ../path_verify.py warnings.json
```
After the path exploration, klee verifies that those two are true positives as:
```
[SrcCode] backlog.c +25
[SrcCode] backlog.c +26
```
Meaning the uninitalized use appears in line 25 and line 26, the details are inside confirm_result.json, KLEE adds the related information of the feasible path. 
### Step4: Information for human to verify the result
The warnings along with the feasible path is in confirm_result.json, the field "path" and "input_0" helps for the human verification.
```json
{
"path":["false :   br i1 %tobool, label %backlog.llbc-test-1, label %backlog.llbc-test-2, !dbg !37"],
"input_0":"#x0000000000000000"},
......
}

- path: feasible path found by klee: in the first branch, the path goes to the false branch
- input_0: when input is 0 (#x0000000000000000), this path is feasible
```
## Prepare LLVM bitcode files of OS kernels
* The code should be compiled with the built LLVM
* We use the github repo and the wrapper to compile the kernel code
* Please follow the compilation instructions in https://github.com/YizhuoZhai/lll-414.git
* After compilation,run the getbclist.py under lll-414/ to get bitcode.list and conduct the experiment for Linux v4.14
