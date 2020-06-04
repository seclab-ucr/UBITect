/***--KQuery2Z3.cpp--**********************************************
 *
 * The implementation for KQuery2Z3.h,complete convert kquery to z3 expr
 *
 *
 */

#include "KQuery2Z3.h"

#include <llvm/ADT/APFloat.h>
#include <llvm/Support/Casting.h>
#include <z3_api.h>
#include <cassert>
#include <iostream>
#include <iterator>
#include <sstream>

#define INT_ARITHMETIC 0


using namespace klee;
using namespace z3;
using namespace llvm;

//we also use namespace std, z3

//constructor
KQuery2Z3::KQuery2Z3(std::vector<ref<Expr> > &_kqueryExpr, z3::context &_z3_ctx) :
        kqueryExpr(_kqueryExpr), z3_ctx(_z3_ctx) {

}

KQuery2Z3::KQuery2Z3(z3::context &_z3_ctx) :
        z3_ctx(_z3_ctx) {

}

KQuery2Z3::~KQuery2Z3() {

}

int KQuery2Z3::validNum(std::string &str) {
    //get the valid number after dot notation of a float point.
    int len = str.length();
    int start = 0;
    int end = len;
    int res = 0;
    for (int i = 0; i < len; i++) {
        if (str[i] == '.') {
            start = i;
            break;
        }
    }
    for (int i = (len - 1); i >= 0; i--) {
        if (str[i] != '0' || str[i] == '.') {
            end = i;
            break;
        }
    }
    res = end - start;
    return res;
}

void KQuery2Z3::getFraction(double dvar, Fraction &frac) {
    //get double value's numerator and denomerator
    //this implementation could crash when the valid number after the dot
    //too many,like .1234545677788.... that makes temp overflow,must fix.
    int numerator = (int) dvar;
    double left = dvar - (double) numerator;
    int denomerator = 0;
    std::stringstream ss;
    ss << left;
    std::string str = ss.str();
    int times = validNum(str);
    int temp = 1;
    for (int i = 0; i < times; i++) {
        temp *= 10;
    }

    numerator = (int) (dvar * temp);
    denomerator = temp;
    frac.num = numerator;
    frac.den = denomerator;
}

void KQuery2Z3::getZ3Expr() {
//	std::cerr << "execute in getZ3Expr\n";
//	std::cerr << "size = " << kqueryExpr.size() << std::endl;
    std::vector<ref<Expr> >::iterator biter = kqueryExpr.begin();
    std::vector<ref<Expr> >::iterator eiter = kqueryExpr.end();
    for (; biter != eiter; biter++) {
//		biter->get()->dump();
        vecZ3Expr.push_back(eachExprToZ3(*biter));
    }
}

z3::expr KQuery2Z3::eachExprToZ3(ref<Expr> &ele) {
    z3::expr res = z3_ctx.bool_val(true);
#if DEBUGINFO
    ele->dump();
#endif
    switch (ele->getKind()) {

        case Expr::Constant: {
            ConstantExpr *ce = cast<ConstantExpr>(ele);
            Expr::Width width = ce->getWidth();

            if (width == Expr::Bool) {
                if (ce->isTrue()) {
                    //that is true
                    res = z3_ctx.bool_val(true);
                } else {
                    //that is false
                    res = z3_ctx.bool_val(false);
                }
            } else if (width != Expr::Fl80) {
                int temp = ce->getZExtValue();
//					std::cerr << "temp = " << temp << std::endl;
#if INT_ARITHMETIC
                res = z3_ctx.int_val(temp);
#else
                res = z3_ctx.bv_val(temp, BIT_WIDTH);
#endif
#if DEBUGINFO
                std::cerr << "case Expr::Constant: " << res << std::endl;
#endif
            } else {
                assert(0 && "The Fl80 out, value bit number extends 64");
            }
            return res;
        }

        case Expr::NotOptimized: {
            assert(0 && "don't handle NotOptimized expression");
            return res;
        }

        case Expr::Read: {
            //type char
            ReadExpr *re = cast<ReadExpr>(ele);
            assert(re && re->updates.root);
            const std::string varName = re->updates.root->name;
            if (re->getWidth() == Expr::Bool) {
                res = z3_ctx.bool_const(varName.c_str());
//            } else if (re->getWidth() == Expr::Int8) {
//                res = z3_ctx.bool_const(varName.c_str());
            } else {
#if INT_ARITHMETIC
                res = z3_ctx.constant(varName.c_str(), z3_ctx.int_sort());
#else
                res = z3_ctx.constant(varName.c_str(), z3_ctx.bv_sort(BIT_WIDTH));
#endif

            }
            return res;
        }

        case Expr::Select: {
            SelectExpr *se = cast<SelectExpr>(ele);

            z3::expr cond = eachExprToZ3(se->cond);
            z3::expr tExpr = eachExprToZ3(se->trueExpr);
            z3::expr fExpr = eachExprToZ3(se->falseExpr);
            if(cond.get_sort().is_bool()){
                res = z3::ite(cond, tExpr, fExpr);
            } else {
                res = z3::ite(cond != 0, tExpr, fExpr);
            }
            return res;
        }

        case Expr::Concat: {
            ConcatExpr *ce = cast<ConcatExpr>(ele);
            ReadExpr *re = NULL;
            if (ce->getKid(0)->getKind() == Expr::Read)
                re = cast<ReadExpr>(ce->getKid(0));
            else if (ce->getKid(1)->getKind() == Expr::Read)
                re = cast<ReadExpr>(ce->getKid(1));
            else
                assert("file: kQuery2z3, Expr::Concat" && false);
            const std::string varName = re->updates.root->name;
#if INT_ARITHMETIC
            res = z3_ctx.constant(varName.c_str(), z3_ctx.int_sort());
#else
            res = z3_ctx.constant(varName.c_str(), z3_ctx.bv_sort(BIT_WIDTH));
#endif
            return res;
        }

            //Trunc and FPTrunc and FPtoSI and FPtoUI
        case Expr::Extract: {
            ExtractExpr *ee = cast<ExtractExpr>(ele);
            z3::expr src = eachExprToZ3(ee->expr);

//			std::cerr << "print in the Extract in kquery2z3\n";
//			ele->dump();
//			ee->expr.get()->dump();

            //convert to boolean value, that means the result
            //depends on the ExtractExpr's least significant
            //bytes.
            if (0 && ee->width == Expr::Bool) {
                //handle int->bool the special
#if INT_ARITHMETIC
                res = z3::ite(src, z3_ctx.int_val(1), z3_ctx.int_val(0));
#else
                res = z3::ite(
//					z3::to_expr(z3_ctx, Z3_mk_extract(z3_ctx, 0, 0, src)),
                        (src != 0),
                        z3_ctx.bv_val(1, BIT_WIDTH), z3_ctx.bv_val(0, BIT_WIDTH));
#endif

            } else {
                res = src;
            }
            return res;
        }

            //ZExt SExt handle methods from encode.cpp
        case Expr::ZExt: {
            CastExpr *ce = cast<CastExpr>(ele);
            z3::expr src = eachExprToZ3(ce->src);
#if DEBUGINFO
            std::cerr << "src : " << src << "\nsrc.get_sort() : " << src.get_sort() << std::endl;
#endif
            if (ce->src.get()->getWidth() == Expr::Bool && src.get_sort().is_bool()) {
#if INT_ARITHMETIC
                res = z3::ite(src, z3_ctx.int_val(1), z3_ctx.int_val(0));
#else
                res = z3::ite((src), z3_ctx.bv_val(1, BIT_WIDTH), z3_ctx.bv_val(0, BIT_WIDTH));
//				res = z3::ite(
//					z3::to_expr(z3_ctx, Z3_mk_extract(z3_ctx, 0, 0, src)),
//					z3_ctx.bool_val(true), z3_ctx.bool_val(false));
#endif
//			if (Z3_TRUE == Z3_algebraic_is_zero(z3_ctx, src)) {
//				res = z3_ctx.bool_val(false);
//			} else {
//				res = z3_ctx.bool_val(true);
//			}
            } else {
                res = src;
            }
#if DEBUGINFO
            std::cerr << "case Expr::ZExt: " << res << "\nce->width : " << ce->width << std::endl;
#endif
            return res;
        }

        case Expr::SExt: {
            CastExpr *ce = cast<CastExpr>(ele);
            z3::expr src = eachExprToZ3(ce->src);
            if (ce->src.get()->getWidth() == Expr::Bool
                && ce->width != Expr::Bool) {
#if INT_ARITHMETIC
                res = z3::ite(src, z3_ctx.int_val(1), z3_ctx.int_val(0));
#else
                res = z3::ite(src, z3_ctx.bv_val(1, BIT_WIDTH), z3_ctx.bv_val(0, BIT_WIDTH));
#endif
            } else {
                res = src;
            }
            return res;
        }

        case Expr::Add: {
            AddExpr *ae = cast<AddExpr>(ele);
            z3::expr left = eachExprToZ3(ae->left);
            z3::expr right = eachExprToZ3(ae->right);
#if DEBUGINFO
            std::cerr << "left: " << left.get_sort() << std::endl;
            std::cerr << "right : " << right.get_sort() << std::endl;
#endif
            res = left + right;
            return res;
        }

        case Expr::Sub: {
            SubExpr *se = cast<SubExpr>(ele);
            z3::expr left = eachExprToZ3(se->left);
            z3::expr right = eachExprToZ3(se->right);
            res = left - right;
            return res;
        }

        case Expr::Mul: {
            MulExpr *me = cast<MulExpr>(ele);
            z3::expr left = eachExprToZ3(me->left);
            z3::expr right = eachExprToZ3(me->right);
            res = left * right;
            return res;
        }

        case Expr::UDiv: {
            //could handled with SDiv, but for test just do in here.
            UDivExpr *ue = cast<UDivExpr>(ele);
            z3::expr left = eachExprToZ3(ue->left);
            z3::expr right = eachExprToZ3(ue->right);
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvudiv(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_div(z3_ctx, left, right));
            }
            return res;
        }

        case Expr::SDiv: {
            SDivExpr *se = cast<SDivExpr>(ele);
            z3::expr left = eachExprToZ3(se->left);
            z3::expr right = eachExprToZ3(se->right);
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvsdiv(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_div(z3_ctx, left, right));
            }

            return res;
        }

        case Expr::URem: {
            URemExpr *ur = cast<URemExpr>(ele);
            z3::expr left = eachExprToZ3(ur->left);
            z3::expr right = eachExprToZ3(ur->right);
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvurem(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_rem(z3_ctx, left, right));
            }
            return res;
        }

        case Expr::SRem: {
            SRemExpr *sr = cast<SRemExpr>(ele);
            z3::expr left = eachExprToZ3(sr->left);
            z3::expr right = eachExprToZ3(sr->right);
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvsrem(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_rem(z3_ctx, left, right));
            }
            return res;
        }

        case Expr::Not: {
            NotExpr *ne = cast<NotExpr>(ele);
            res = eachExprToZ3(ne->expr);
            if (res.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvnot(z3_ctx, res));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_not(z3_ctx, res));
            }
            return res;
        }

        case Expr::And: {
            AndExpr *ae = cast<AndExpr>(ele);
            z3::expr left = eachExprToZ3(ae->left);
            z3::expr right = eachExprToZ3(ae->right);
//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::And\n");
//			std::cerr << "And left = " << left << std::endl;
//			std::cerr << "And right = " << right << std::endl;
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvand(z3_ctx, left, right));
            } else {
//				std::cerr << "left = " << left << ", left sort = " << left.get_sort() << std::endl;
//				std::cerr << "right = " << right << ", right sort = " << right.get_sort() << std::endl;
#if INT_ARITHMETIC
                if (left.is_int()) {
                    z3::expr tempLeft = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, left));
//						std::cerr << "tempLeft = " << tempLeft << std::endl;
                    z3::expr tempRight = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, right));
//						std::cerr << "tempRight = " << tempRight << std::endl;

                    z3::expr tempRes = z3::to_expr(z3_ctx, Z3_mk_bvand(z3_ctx, tempLeft, tempRight));
//						std::cerr << "tempRes = " << tempRes << std::endl;
                    res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
//						std::cerr << "res = " << res << std::endl;
                } else {
                    res = left && right;
                }
#else
                res = left && right;
#endif
            }
            return res;
        }


        case Expr::Or: {
            OrExpr *oe = cast<OrExpr>(ele);
            z3::expr left = eachExprToZ3(oe->left);
            z3::expr right = eachExprToZ3(oe->right);

//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Or\n");

            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvor(z3_ctx, left, right));
            } else {
#if INT_ARITHMETIC
                if (left.is_int()) {
                    z3::expr tempLeft = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, left));
                    z3::expr tempRight = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, right));
                    z3::expr tempRes = z3::to_expr(z3_ctx, Z3_mk_bvor(z3_ctx, tempLeft, tempRight));
                    res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
                } else {
                    res = left || right;
                }
#else
                res = left || right;
#endif
            }
            return res;
        }


        case Expr::Xor: {
            XorExpr *xe = cast<XorExpr>(ele);
            z3::expr left = eachExprToZ3(xe->left);
            z3::expr right = eachExprToZ3(xe->right);

//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Xor\n");
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvxor(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_xor(z3_ctx, left, right));
            }
            return res;
        }

            //following shift operation must be bitvector operand.
        case Expr::Shl: {
            ShlExpr *se = cast<ShlExpr>(ele);
            z3::expr left = eachExprToZ3(se->left);
            z3::expr right = eachExprToZ3(se->right);
            //convert bit vector to int in order to binary operation.
//		assert(
//				left.get_sort() == right.get_sort()
//						&& "sort between left and right are different in Expr::Shl\n");
#if INT_ARITHMETIC
            z3::expr tempLeft = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, left));
            z3::expr tempRight = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, right));

            z3::expr tempRes = z3::to_expr(z3_ctx, Z3_mk_bvshl(z3_ctx, tempLeft, tempRight));
            res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
#else
            res = z3::to_expr(z3_ctx, Z3_mk_bvshl(z3_ctx, left, right));
//		res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
#endif


            return res;
        }

        case Expr::LShr: {
            LShrExpr *lse = cast<LShrExpr>(ele);
            z3::expr left = eachExprToZ3(lse->left);
            z3::expr right = eachExprToZ3(lse->right);
//		assert(
//				left.get_sort() == right.get_sort()
//						&& "sort between left and right are different in Expr::LShr\n");
#if INT_ARITHMETIC
            z3::expr tempLeft = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, left));
            z3::expr tempRight = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, right));
            z3::expr tempRes = z3::to_expr(z3_ctx, Z3_mk_bvlshr(z3_ctx, tempLeft, tempRight));
            res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
#else
            res = z3::to_expr(z3_ctx, Z3_mk_bvlshr(z3_ctx, left, right));
//		res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
#endif

            return res;
        }

        case Expr::AShr: {
            AShrExpr *ase = cast<AShrExpr>(ele);
            z3::expr left = eachExprToZ3(ase->left);
            z3::expr right = eachExprToZ3(ase->right);
//		assert(
//				left.get_sort() == right.get_sort()
//						&& "sort between left and right are different in Expr::AShr\n");
#if INT_ARITHMETIC
            z3::expr tempLeft = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, left));
            z3::expr tempRight = z3::to_expr(z3_ctx, Z3_mk_int2bv(z3_ctx, BIT_WIDTH, right));
            z3::expr tempRes = z3::to_expr(z3_ctx, Z3_mk_bvashr(z3_ctx, tempLeft, tempRight));
            res = z3::to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, tempRes, true));
#else
            auto temp = Z3_mk_bvashr(z3_ctx, left, right);
#if DEBUGINFO
            std::cout << "Z3_get_ast_kind : " << Z3_get_ast_kind(z3_ctx, temp) << std::endl;
#endif
            res = z3::to_expr(z3_ctx, temp);
#endif

            return res;
        }

        case Expr::Eq: {
            EqExpr *ee = cast<EqExpr>(ele);
            z3::expr left = eachExprToZ3(ee->left);
            z3::expr right = eachExprToZ3(ee->right);
//			assert(
//					Z3_get_sort_kind(z3_ctx, left)
//							&& "sort between left and right are different in Expr::Eq\n");
//			std::cerr << "ee left = " << ee->left << std::endl;
//			std::cerr << "ee right = " << ee->right << std::endl;


//			std::cerr << "left = " << left << ", left sort = " << left.get_sort() << std::endl;
//			std::cerr << "right = " << right << ", right sort = " << right.get_sort() << std::endl;
            res = (left == right);
//
//            std::cerr << "res = " << res << " sort : " << res.get_sort() << std::endl;

            if(res.get_sort()){
            } else {
                res = z3_ctx.bool_val(false);
            }

            return res;
        }

        case Expr::Ult: {
            //probably can float point value's comparison.
            UltExpr *ue = cast<UltExpr>(ele);
            z3::expr left = eachExprToZ3(ue->left);
            z3::expr right = eachExprToZ3(ue->right);
//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Ult\n");
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvult(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_lt(z3_ctx, left, right));
            }
            return res;
        }


        case Expr::Ule: {
            UleExpr *ue = cast<UleExpr>(ele);
            z3::expr left = eachExprToZ3(ue->left);
            z3::expr right = eachExprToZ3(ue->right);

//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Ule\n");
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvule(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_le(z3_ctx, left, right));
            }
            return res;
        }
        case Expr::Slt: {
            SltExpr *se = cast<SltExpr>(ele);
            z3::expr left = eachExprToZ3(se->left);
            z3::expr right = eachExprToZ3(se->right);

//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Slt\n");
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvslt(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_lt(z3_ctx, left, right));
            }
            return res;
        }
        case Expr::Sle: {
            SleExpr *se = cast<SleExpr>(ele);
            z3::expr left = eachExprToZ3(se->left);
            z3::expr right = eachExprToZ3(se->right);

//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Sle\n");
            if (left.is_bv()) {
                res = z3::to_expr(z3_ctx, Z3_mk_bvsle(z3_ctx, left, right));
            } else {
                res = z3::to_expr(z3_ctx, Z3_mk_le(z3_ctx, left, right));
            }
            return res;
        }

        case Expr::Ne: {
            NeExpr *ne = cast<NeExpr>(ele);
            z3::expr left = eachExprToZ3(ne->left);
            z3::expr right = eachExprToZ3(ne->right);

//			assert(
//					left.get_sort() == right.get_sort()
//							&& "sort between left and right are different in Expr::Ne\n");

            res = (left != right);
            return res;
        }

            //stp unhandled type
            /*	  case Expr::Ne:
             case Expr::Ugt:
             case Expr::Uge:
             case Expr::Sgt:
             case Expr::Sge:
             */
        default:
            assert(0 && "unhandled Expr type in kueryExpr to Z3Expr");
            return res;

    }
    std::cerr << "end of switch\n";
    return res;
}

void KQuery2Z3::printZ3AndKqueryExpr() {
    int size = vecZ3Expr.size();

    for (int i = 0; i < size; i++) {
        kqueryExpr[i].get()->dump();
        std::cerr << "--------------------\n";
        std::cerr << vecZ3Expr[i] << std::endl;
        std::cerr << "++++++++++++++++++++\n";
    }
}

void KQuery2Z3::printKquery() {
    int size = vecZ3Expr.size();
    std::cerr << "vec size of vecZ3Expr = " << size << std::endl;
    for (int i = 0; i < size; i++) {
        kqueryExpr[i]->dump();
    }
}

z3::expr KQuery2Z3::getZ3Expr(ref<Expr> &e) {
    z3::expr res = eachExprToZ3(e);
    return res;
}
