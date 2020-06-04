find_package(LLVM REQUIRED CONFIG)

list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_VERSION} -fno-rtti")
include_directories(${LLVM_INCLUDE_DIRS})
#add_library(myHello MODULE Hello.cpp)
add_subdirectory(bbTag)
