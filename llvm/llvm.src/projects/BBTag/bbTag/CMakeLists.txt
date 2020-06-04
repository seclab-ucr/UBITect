add_library(bbTag MODULE bbTag.cpp)
add_llvm_loadable_module(bbTaglib
	bbTag.cpp
)
