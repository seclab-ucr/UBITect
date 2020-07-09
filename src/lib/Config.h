//
// Created by ubuntu on 11/28/17.
//

#ifndef UBIANALYSIS_CONFIG_H
#define UBIANALYSIS_CONFIG_H
#include <stack>
#include "Common.h"
#define _ID 1
#define _UD 0
// Setup functions for heap allocations.
static void SetHeapAllocFuncs(
        std::set<std::string> &HeapAllocFuncs){

    std::string HeapAllocFN[] = {
        "__kmalloc",
        "__vmalloc",
        "vmalloc",
        "krealloc",
        "devm_kzalloc",
        "vzalloc",
        "malloc",
        "kmem_cache_alloc",
        "__alloc_skb",
    };

    for (auto F : HeapAllocFN) {
        HeapAllocFuncs.insert(F);
    }
}
static void SetZeroMallocFuncs(
        std::set<std::string> &ZeroMallocFuncs) {
    std::string ZeroAllocFN[] = {
            "kzalloc",
    };
    for (auto F : ZeroAllocFN) {
        ZeroMallocFuncs.insert(F);
    }
}
static void SetTransferFuncs(
		std::set<std::string> &TransferFuncs) {
    std::string TransferFN[] = {
        "copy_to_user",
        "__copy_to_user",
        "copy_from_user",
        "__copy_from_user",
    };
    for (auto F : TransferFN) {
        TransferFuncs.insert(F);
    }
}
static void SetCopyFuncs(
		std::set<std::string> &CopyFuncs) {
    std::string CopyFN[] = {
        "memcpy",
	    "llvm.memcpy.p0i8.p0i8.i32",
	    "llvm.memcpy.p0i8.p0i8.i64",
	    "memmove",
	    "llvm.memmove.p0i8.p0i8.i32",
	    "llvm.memmove.p0i8.p0i8.i64",
    };
	for (auto F : CopyFN) {
        CopyFuncs.insert(F);
    }
}
static void SetInitFuncs(
        std::set<std::string> &InitFuncs){
    std::string InitFN[] = {
	"llvm.va_start",
        "memset",
        "llvm.memset.p0i8.i32",
        "llvm.memset.p0i8.i64",
    };
    for (auto F : InitFN) {
        InitFuncs.insert(F);
    }
}
static void SetOtherFuncs(
        std::set<std::string> &OtherFuncs){
    std::string OtherFN[] = {
        "mcount",
        "llvm.dbg.declare",
	"llvm.dbg.value",
	"llvm.dbg.addr",
    };
    for (auto F : OtherFN) {
        OtherFuncs.insert(F);
    }
}
static void SetObjSizeFuncs(
        std::set<std::string> &ObjSizeFuncs){
    std::string ObjSizeFN[] = {
        "llvm.objectsize.i64.p0i8",
    };
    for (auto F : ObjSizeFN) {
        ObjSizeFuncs.insert(F);
    }
}
static void SetStrFuncs(
        std::set<std::string> &StrFuncs){
    std::string StrFN[] = {
        "strcmp",
	"strncmp",
	"strcpy",
	"strlwr",
	"strcat",
	"strlen",
	"strupr",
	"strrchr",
	"strncat",
    };
    for (auto F : StrFN) {
        StrFuncs.insert(F);
    }
}
//10 candidates of the inderect caller which could be checked by casting
static void SetIndirectFuncs(
        std::set<std::string> &indirectFuncs){
    std::string IndirectFN[] = {
	"kvm_vfio_group_is_coherent",
        //"kvm_vfio_external_group_match_file",
	//"kvm_device_ioctl_attr",
	//"kvm_device_ioctl",
	//"kvm_destroy_devices",
	//"sctp_inq_push",
	//"kvm_arch_vcpu_unblocking",
	//"kvm_vcpu_ioctl_set_cpuid2",
	//"hda_call_check_power_status",
	//"restore_mixer_state",
    };
    for (auto F : IndirectFN) {
        indirectFuncs.insert(F);
    }
}
#ifdef FindAlloc
llvm::Value *FindAlloc(llvm::Value *V)
{
	if (llvm::Instruction *I = dyn_cast<Instruction>(V))
	{
		switch(I->getOpCode())
		{
			case Instruction::Alloca:
			case Instruction::Add:
       			case Instruction::FAdd:
       			case Instruction::Sub:
       			case Instruction::FSub:
       			 case Instruction::Mul:
       			 case Instruction::FMul:
       			 case Instruction::SDiv:
       			 case Instruction::UDiv:
       			 case Instruction::FDiv:
       			 case Instruction::SRem:
       			 case Instruction::URem:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Xor:
        case Instruction::LShr:
        case Instruction::AShr:
        case Instruction::Shl:
			{
				return I;
			}
			case Instruction::Load:
			case Instruction::SExt:
       			case Instruction::ZExt:
			case Instruction::Trunc:	
			case Instruction::IntToPtr:
			case Instruction::PtrToInt:
			case Instruction::Select:
			{
				return FindAlloc(I->getOperand(0));
			}
			case Instruction::GetElementPtr:
			{
				return FindAlloc(I->getOperand(0));
			}
			
	
		}//wsitch
	}
}
#endif



#endif //UBIANALYSIS_CONFIG_H
