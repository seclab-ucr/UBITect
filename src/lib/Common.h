//
// Created by ubuntu on 2/5/18.
//

#ifndef UBIANALYSIS_COMMON_H
#define UBIANALYSIS_COMMON_H
#include <llvm/Support/raw_ostream.h>
#include "FunctionSummary.h"


/*#define HT_LOG(lv, stmt)							\
	do {											\
		if (VerboseLevel >= lv)						\
			errs() << stmt;							\
	} while(0)

#define AA_LOG(stmt) HT_LOG(2, stmt)*/
#define OP errs()

#include <unordered_map>

#define FUNCTION_TIMER()
#endif //UBIANALYSIS_COMMON_H
