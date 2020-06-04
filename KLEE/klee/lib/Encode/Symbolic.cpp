/*
 * Symbolic.cpp
 *
 *  Created on: Oct 22, 2018
 *      Author: klee
 */

#include "Symbolic.h"

#include <llvm/IR/CallSite.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/raw_ostream.h>
#include <cassert>
#include <sstream>
#include <utility>

#include "../../include/klee/Internal/Module/KInstruction.h"
#include "../Core/AddressSpace.h"
#include "../Core/Executor.h"
#include "../Core/Memory.h"
#include "Encode.h"

#include <llvm/IR/Constant.h>
#include <llvm/IR/Instruction.h>
#include <llvm/Support/Casting.h>
#include <cassert>
#include <iostream>
#include <iterator>
#include <map>
#include <sstream>
#include <utility>
#include "../../include/klee/Internal/Module/KInstruction.h"

namespace klee {

    Symbolic::Symbolic(Executor *executor) {
        // TODO Auto-generated constructor stub
        this->executor = executor;
    }

    Symbolic::~Symbolic() {
        // TODO Auto-generated destructor stub
    }


    std::string Symbolic::getName(ref<klee::Expr> value) {
        ReadExpr *revalue;
        if (value->getKind() == Expr::Concat) {
            ConcatExpr *ccvalue = cast<ConcatExpr>(value);
            revalue = cast<ReadExpr>(ccvalue->getKid(0));
        } else if (value->getKind() == Expr::Read) {
            revalue = cast<ReadExpr>(value);
        } else {
            assert(0 && "getGlobalName");
        }
        std::string globalName = revalue->updates.root->name;
        return globalName;
    }

    void Symbolic::resolveSymbolicExpr(ref<klee::Expr> symbolicExpr, std::set<std::string> &relatedSymbolicExpr) {
        if (symbolicExpr->getKind() == Expr::Read) {
            std::string name = getName(symbolicExpr);
            if (relatedSymbolicExpr.find(name) == relatedSymbolicExpr.end()) {
                relatedSymbolicExpr.insert(name);
            }
            return;
        } else {
            unsigned kidsNum = symbolicExpr->getNumKids();
            if (kidsNum == 2 && symbolicExpr->getKid(0) == symbolicExpr->getKid(1)) {
                resolveSymbolicExpr(symbolicExpr->getKid(0), relatedSymbolicExpr);
            } else {
                for (unsigned int i = 0; i < kidsNum; i++) {
                    resolveSymbolicExpr(symbolicExpr->getKid(i), relatedSymbolicExpr);
                }
            }
        }
    }

    ref<Expr> Symbolic::manualMakeSymbolic(std::string name, unsigned int size) {
#if DEBUGINFO
        llvm::errs() << "manualMakeSymbolic size :" << size << "\n";
#endif
        //添加新的符号变量
        const Array *array = new Array(name, size);
        ObjectState *os = new ObjectState(size, array);
        ref<Expr> offset = ConstantExpr::create(0, BIT_WIDTH);
        ref<Expr> result = os->read(offset, size);
#if DEBUGINFO
        llvm::errs() << "make symboic:" << name << "\n";
        llvm::errs() << "result : ";
        result->dump();
#endif
        return result;
    }

    std::string Symbolic::createGlobalVarFullName(std::string i, unsigned memoryId,
                                                  uint64_t address, bool isGlobal, unsigned time, bool isStore) {
        char signal;
        ss.str("");
        ss << i;
        if (isGlobal) {
            signal = 'G';
        } else {
            signal = 'L';
        }
        ss << signal;
        ss << memoryId;
        ss << '_';
        ss << address;
        if (isStore) {
            signal = 'S';
        } else {
            signal = 'L';
        }
        ss << signal;
        ss << time;
#if DEBUGINFO
        llvm::errs() << "createGlobalVarFullName : " << ss.str() << "\n";
#endif
        return ss.str();
    }

    unsigned Symbolic::getLoadTime(uint64_t address) {
        unsigned loadTime;
        std::map<uint64_t, unsigned>::iterator index = loadRecord.find(address);
        if (index == loadRecord.end()) {
            loadRecord.insert(std::make_pair(address, 1));
            loadTime = 1;
        } else {
            loadTime = index->second + 1;
            loadRecord[address] = loadTime;
        }
        return loadTime;
    }

    unsigned Symbolic::getStoreTime(uint64_t address) {
        unsigned storeTime;
        std::map<uint64_t, unsigned>::iterator index = storeRecord.find(address);
        if (index == storeRecord.end()) {
            storeRecord.insert(std::make_pair(address, 1));
            storeTime = 1;
        } else {
            storeTime = index->second + 1;
            storeRecord[address] = storeTime;
        }
        return storeTime;
    }

    void Symbolic::load(ExecutionState &state, KInstruction *ki) {
        std::string GlobalName;
        bool isGlobal;

        Type::TypeID id = ki->inst->getType()->getTypeID();
        ref<Expr> address = executor->eval(ki, 0, state).value;
        ObjectPair op;
#if DEBUGINFO
        ref<Expr> addressCurrent = executor->eval(ki, 0, state).value;
        llvm::errs() << "address : " << address << " address Current : "
                     << addressCurrent << "\n";
        bool successCurrent = executor->getMemoryObject(op, state,
                                                        &state.addressSpace, addressCurrent);
        llvm::errs() << "successCurrent : " << successCurrent << "\n";
        llvm::errs() << "id : " << id << "\n";
#endif
        ConstantExpr *realAddress = dyn_cast<ConstantExpr>(address);
        if (realAddress) {
            uint64_t key = realAddress->getZExtValue();
            bool success = executor->getMemoryObject(op, state,
                                                     &(state.addressSpace), address);
            if (success) {
                const MemoryObject *mo = op.first;
                isGlobal = executor->isGlobalMO(mo);
                if (isGlobal) {
                    unsigned loadTime = getLoadTime(key);
                    std::string ld;
                    llvm::raw_string_ostream rso(ld);
                    ki->inst->print(rso);
                    std::stringstream ss;
                    unsigned int j = rso.str().find("=");
                    for (unsigned int i = 2; i < j; i++) {
                        ss << rso.str().at(i);
                    }
                    if (mo->isGlobal) {

                    } else {
                        ss << "con";
                    }
                    GlobalName = createGlobalVarFullName(ss.str(), mo->id, key,
                                                         isGlobal, loadTime, false);
                    if (id == Type::IntegerTyID) {
                        Expr::Width size = executor->getWidthForLLVMType(
                                ki->inst->getType());
                        ref<Expr> value = executor->getDestCell(state, ki).value;
                        ref<Expr> symbolic = manualMakeSymbolic(GlobalName, size);
#if DEBUGINFO
                        std::cerr << " load symbolic value : ";
                        symbolic->dump();
#endif
                        executor->bindLocal(ki, state, symbolic);
                        state.encode.globalname.push_back(GlobalName);
                        state.encode.globalexpr.push_back(symbolic);
                    } else {
                        Expr::Width size = executor->getWidthForLLVMType(
                                ki->inst->getType());
                        ref<Expr> value = executor->getDestCell(state, ki).value;
                        ref<Expr> symbolic = manualMakeSymbolic(GlobalName, size);
#if DEBUGINFO
                        std::cerr << " load symbolic value : ";
                        symbolic->dump();
#endif
                        executor->bindLocal(ki, state, symbolic);
                        state.encode.globalname.push_back(GlobalName);
                        state.encode.globalexpr.push_back(symbolic);
                    }
                }
            } else {
#if DEBUGINFO
                llvm::errs() << "Load address = " << realAddress->getZExtValue()
                             << "\n";
#endif
                std::string ld;
                llvm::raw_string_ostream rso(ld);
                ki->inst->print(rso);
                std::stringstream ss;
                unsigned int j = rso.str().find("=");
                for (unsigned int i = 2; i < j; i++) {
                    ss << rso.str().at(i);
                }
                GlobalName = ss.str() + "erroraddr";
                if (id == Type::IntegerTyID || id == Type::PointerTyID) {
                    Expr::Width size = executor->getWidthForLLVMType(
                            ki->inst->getType());
                    ref<Expr> symbolic = manualMakeSymbolic(GlobalName, size);
                    executor->bindLocal(ki, state, symbolic);
                    ref<Expr> value = executor->getDestCell(state, ki).value;
#if DEBUGINFO
                    std::cerr << " load symbolic value : ";
                    symbolic->dump();
                    std::cerr << " load value : ";
                    value->dump();
#endif
                    state.encode.globalname.push_back(GlobalName);
                    state.encode.globalexpr.push_back(symbolic);
                } else {
                    assert(0 && " address is not const");
                }
            }
        } else {
            std::string ld;
            llvm::raw_string_ostream rso(ld);
            ki->inst->print(rso);
            std::stringstream ss;
            unsigned int j = rso.str().find("=");
            for (unsigned int i = 2; i < j; i++) {
                ss << rso.str().at(i);
            }
            GlobalName = ss.str() + "noaddr";
            if (id == Type::IntegerTyID || id == Type::PointerTyID) {
                Expr::Width size = executor->getWidthForLLVMType(
                        ki->inst->getType());
                ref<Expr> symbolic = manualMakeSymbolic(GlobalName, size);
                executor->bindLocal(ki, state, symbolic);
                ref<Expr> value = executor->getDestCell(state, ki).value;
#if DEBUGINFO
                std::cerr << " load symbolic value : ";
                symbolic->dump();
                std::cerr << " load value : ";
                value->dump();
#endif
                state.encode.globalname.push_back(GlobalName);
                state.encode.globalexpr.push_back(symbolic);
            } else {
                assert(0 && " address is not const");
            }
        }
    }

    void Symbolic::callReturnValue(ExecutionState &state, KInstruction *ki,
                                   Function *function) {
        Type *resultType = ki->inst->getType();
        if (!resultType->isVoidTy()) {
            Expr::Width size = executor->getWidthForLLVMType(ki->inst->getType());
            std::string ld;
            llvm::raw_string_ostream rso(ld);
            ki->inst->print(rso);
            std::stringstream ss;
            unsigned int j = rso.str().find("=");
            for (unsigned int i = 2; i < j; i++) {
                ss << rso.str().at(i);
            }

            std::string GlobalName = ss.str() + "call return";
            ref<Expr> symbolic = manualMakeSymbolic(GlobalName, size);
            executor->bindLocal(ki, state, symbolic);
#if DEBUGINFO
            std::cerr << "ki->dest : " << ki->dest << "\n";
#endif
            state.encode.globalname.push_back(GlobalName);
            state.encode.globalexpr.push_back(symbolic);

            Instruction *i = ki->inst;
            llvm::CallSite cs(i);
            unsigned numArgs = cs.arg_size();
            for (unsigned j = 0; j < numArgs; ++j) {
                std::string argName = ss.str() + "call arg" + std::to_string(j);
                Expr::Width size = executor->getWidthForLLVMType(cs.getArgument(j)->getType());
                ref<Expr> arg = manualMakeSymbolic(argName, size);
                executor->uneval(ki, j + 1, state).value = arg;
#if DEBUGINFO
                std::cerr << "argName : " << argName << "\n";
                std::cerr << "size : " << size << "\n";
                std::cerr << "arg : ";
                arg->dump();
#endif
            }
        }
    }

    void Symbolic::Alloca(ExecutionState &state, KInstruction *ki, unsigned size) {
        AllocaInst *ai = cast<AllocaInst>(ki->inst);
        if(this->executor->eval(ki, 0, state).value->getKind() != Expr::Constant){
            return;
        }
        if (ai->getAllocatedType()->getTypeID() == Type::IntegerTyID) {
            ref<Expr> symbolic = manualMakeSymbolic(allocaName, size * 8);

            ObjectPair op;
            ref<Expr> address = this->executor->getDestCell(state, ki).value;
            ConstantExpr *realAddress = dyn_cast<ConstantExpr>(address);
            if (realAddress) {
                bool success = executor->getMemoryObject(op, state,
                                                         &(state.addressSpace), address);
                if (success) {
                    const MemoryObject *mo = op.first;
                    ref<Expr> offset = mo->getOffsetExpr(address);
                    const ObjectState *os = op.second;
                    if (os->readOnly) {
                    } else {
                        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                        wos->write(offset, symbolic);
                    }
                }
            }

        } else if (ai->getAllocatedType()->getTypeID() == Type::PointerTyID) {
            ref<Expr> symbolic = manualMakeSymbolic(allocaName, BIT_WIDTH);

            ObjectPair op;
            ref<Expr> address = this->executor->getDestCell(state, ki).value;
            ConstantExpr *realAddress = dyn_cast<ConstantExpr>(address);
            if (realAddress) {
                bool success = executor->getMemoryObject(op, state,
                                                         &(state.addressSpace), address);
                if (success) {
                    const MemoryObject *mo = op.first;
                    ref<Expr> offset = mo->getOffsetExpr(address);
                    const ObjectState *os = op.second;
                    if (os->readOnly) {
                    } else {
                        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
                        wos->write(offset, symbolic);
                    }
                }
            }
        } else {
#if DEBUGINFO
            std::cerr << "Alloca state.encode.ckeck = false;" << "\n";
#endif
            state.encode.ckeck = false;
        }
    }

    int Symbolic::checkInst(ExecutionState &state, KInstruction *ki) {

//        return 0;
#if DEBUGINFO
        std::cerr << "checkInst : " << "\n";
#endif
        if (!state.encode.ckeck) {
            return 0;
        }

        int res = -1;

        llvm::Instruction *inst = ki->inst;

        if (inst->getOpcode() == Instruction::Load) {
            ref<Expr> base = this->executor->eval(ki, 0, state).value;
            ObjectPair op;
            bool success = executor->getMemoryObject(op, state, &(state.addressSpace), base);
            if (success) {
            } else {
                res = 0;
                return res;
            }
        } else if (inst->getOpcode() == Instruction::Alloca) {
        } else if (inst->getOpcode() == Instruction::PHI) {
        } else if (inst->getOpcode() == Instruction::Store) {

            ref<Expr> base = this->executor->eval(ki, 1, state).value;
            ObjectPair op;
            bool success = executor->getMemoryObject(op, state, &(state.addressSpace), base);
            if (success) {
            } else {
                res = 0;
                return res;
            }

            ref<Expr> v = this->executor->eval(ki, 0, state).value;
#if DEBUGINFO
            v->dump();
#endif
            if (v->getKind() == Expr::Concat) {
                ConcatExpr *vv = cast<ConcatExpr>(v);
                ReadExpr *revalue = cast<ReadExpr>(vv->getKid(0));
                std::string name = revalue->updates.root->name;
                if (name == allocaName) {
                    res = 0;
                    return res;
                }
            } else if(v->getKind() != Expr::Constant){
                std::set<std::string> relatedSymbolicExpr;
                resolveSymbolicExpr(v, relatedSymbolicExpr);
                for(auto name : relatedSymbolicExpr) {
                    if (name == allocaName) {
                        res = 0;
                        return res;
                    }
                }
            }

//            if (v->getKind() != Expr::Constant) {
//                res = 0;
//            }

        } else {

            uint64_t num = inst->getNumOperands();
#if DEBUGINFO
            std::cerr << "inst->getOpcode() : " << inst->getOpcode() << "\n";
            std::cerr << "num : " << num << "\n";
#endif
            for (uint64_t idx = 0; idx < num; idx++) {
                if (inst->getOperand(idx)->getType()->getTypeID() == Type::IntegerTyID ||
                    inst->getOperand(idx)->getType()->getTypeID() == Type::PointerTyID) {
                    int vnumber = ki->operands[idx];
                    if (vnumber == -1) {
                        break;
                    }
                    ref<Expr> v = this->executor->eval(ki, idx, state).value;
#if DEBUGINFO
                    std::cerr << "operand : " << idx << "\n";
                    v->dump();
#endif
                    if (v->getKind() == Expr::Concat) {
                        ConcatExpr *vv = cast<ConcatExpr>(v);
                        ReadExpr *revalue = cast<ReadExpr>(vv->getKid(0));
                        std::string name = revalue->updates.root->name;
                        if (name == allocaName) {
                            res = 0;
                            return res;
                        }
                    } else if(v->getKind() != Expr::Constant){
                        std::set<std::string> relatedSymbolicExpr;
                        resolveSymbolicExpr(v, relatedSymbolicExpr);
                        for(auto name : relatedSymbolicExpr) {
                            if (name == allocaName) {
                                res = 0;
                                return res;
                            }
                        }
                    }

//                    if (v->getKind() != Expr::Constant) {
//                        res = 0;
//                    }

                }
            }
        }
        return res;
    }

    int Symbolic::isWarning(ExecutionState &state, KInstruction *ki) {
        llvm::Instruction *inst = ki->inst;
        std::string ld;
        llvm::raw_string_ostream rso(ld);
        inst->print(rso);
        std::stringstream ss;
        unsigned int j = rso.str().find("!");
        if (j >= rso.str().size()) {
            for (unsigned int i = 0; i < rso.str().size(); i++) {
                ss << rso.str().at(i);
            }
        } else {
            for (unsigned int i = 0; i < j; i++) {
                ss << rso.str().at(i);
            }
        }

#if DEBUGINFO
        std::cerr << "isWarning : " << "\n";
        std::cerr << state.encode.warning << std::endl;
        std::cerr << ss.str() << std::endl;
        std::cerr << inst->getParent()->getName().str() << std::endl;
#endif
        if (state.encode.warning.compare(ss.str()) == 0) {
#if DEBUGINFO
            std::cerr << "state.encode.warning.compare : 0" << "\n";
#endif
            return 1;
        } else {
#if DEBUGINFO
            std::cerr << "state.encode.warning.compare : !0" << "\n";
#endif
        }
        return 0;
    }

} /* namespace klee */
