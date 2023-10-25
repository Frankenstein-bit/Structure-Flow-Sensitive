**MTO-SS Experiment**

This project contains all the code and experimental materials needed for the paper titled "Structure-Sensitive Points-to Analysis for Multi-structure Objects". The objective of this experiment is to demonstrate the accuracy of MTO-SS pointer analysis and its additional performance overhead.

**Dependencies**
- llvm-13.0.1
- z3-4.8.8
- ctir-clang-v10.c3-ubuntu18.04

Ensure that these are set up as environment variables. Additionally, clone this project and set the project directory as an environment variable. For example:

```bash
export LLVM_HOME=/home/*/clang+llvm-13.0.1-x86_64-linux-gnu-ubuntu-18.04/bin
export PATH=$LLVM_HOME:$PATH
export LLVM_DIR=/home/*/clang+llvm-13.0.1-x86_64-linux-gnu-ubuntu-18.04
export PATH=$LLVM_DIR:$PATH
export Z3_DIR=/home/*/z3-4.8.8-x64-ubuntu-16.04
export CTIR_DIR=/home/*/ctir-clang-v10.c3-ubuntu18.04/bin
export SVF_DIR=/home/*/Structure-Flow-Sensitive
```

Note: Our project is based on SVF-2.5. For more information, please visit [SVF-tools/SVF on GitHub](https://github.com/SVF-tools/SVF/).

**Running MTO-SS**

Navigate to the directory where the project resides and execute:
```bash
./build.sh debug
```

The generated files can be found under the `bin` directory, with the filename `wpa`. Files used for evaluation are located in the `GNU-Coreutils-test12` folder. To run an example:

```bash
./wpa Structure-Flow-Sensitive/GNU-Coreutils-test12/csplit.0.5.precodegen.bc
```

This will produce evaluation results.

**Learning about the MTO-SS Project**:
The SVF-2.5 project is quite complex. The main files involved in our project include:
- FlowSensitiveStruct.cpp 
- FlowSensitiveStruct.h
- PointerAnalysis.h
- PointerAnalysis.cpp
- SVFIR.cpp
- MemoryModel/SVFIR.h
