set (UBITectSourceCodes
	CRange.h
	TaintSignature.h
	IntGlobal.h
	UBIAnalysis.h
	UBIAnalysis.cpp
	CallGraph.h
	CallGraph.cpp
	Common.h
	Config.h
	PtsSet.h
	Helper.h
	Helper.cpp
	StructAnalyzer.h
	StructAnalyzer.cpp
	Annotation.h
	Annotation.cpp
	NodeFactory.h
	NodeFactory.cpp
	QualifierAnalysis.h
	QualifierAnalysis.cpp
	QualiInference.cpp
	QualifierCheck.cpp
	ConstraintCollect.cpp
	AAMap.cpp
	FuncProcess.cpp
	FunctionSummary.h
	json.hpp
	json11.hpp
	json11.cpp
)

# Build libraries.
add_library (UBITectObj OBJECT ${UBITectSourceCodes})
add_library (UBITect SHARED $<TARGET_OBJECTS:UBITectObj>)
add_library (UBITectStatic STATIC $<TARGET_OBJECTS:UBITectObj>)

# Build executable ubitect.
set (EXECUTABLE_OUTPUT_PATH ${UBITECT_BINARY_DIR})
link_directories (${UBITECT_BINARY_DIR}/lib)
#project (ubitect C CXX)
add_executable(ubitect ${UBITectSourceCodes})
target_link_libraries(ubitect 
  LLVMAsmParser 
  LLVMSupport 
  LLVMCore 
  LLVMAnalysis
  LLVMIRReader
  UBITectStatic
  )
