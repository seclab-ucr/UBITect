#ifndef TAINT_SIGNATURE_H
#define TAINT_SIGNATURE_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/SpecialCaseList.h"

using namespace llvm;

class TaintSignature {
	std::unique_ptr<llvm::SpecialCaseList> SCL;

public:
	TaintSignature(StringRef SignaturePath);

	bool IsSensitiveFunction(StringRef FuncName) const;
	bool IsSensitiveFunctionArg(StringRef FuncName,
								unsigned ArgIndex) const;

	bool isFunctionInSig(bool IsSink, StringRef FuncName) const;
	bool isFunctionArgInSig(bool IsSink, StringRef FuncName,
							unsigned ArgIndex) const;
	bool isFuctionRetInSig(bool IsSink, StringRef FuncName) const;
	bool isSensitiveStruct(StringRef StructId) const;
};

#endif
