/*
 * KQuery2Z3.h
 *
 * Created on: July 3, 2015
 * 		Author: Liu Pei
 *
 * 		This class used to convert the format of KQuery
 * 		to Z3 for convenient solve in Encode.cpp
 *
 * 		The conversion is not complete because not all the instructions
 * 		are used in our processing.
 *
 *
 */

#ifndef KQUERY2Z3_H_
#define KQUERY2Z3_H_

#include <z3++.h>
#include <string>
#include <vector>

#include "../../include/klee/Expr.h"
#include "../../include/klee/util/Ref.h"

#define BIT_WIDTH 64

using namespace z3;
namespace klee {

typedef struct fraction {
	int num;
	int den;
}Fraction;

class KQuery2Z3 {
private:
	//preserve for some private variable and function
	std::vector< ref<Expr> > kqueryExpr;
	//the parameter convert means convert a none float point
	//to a float point.
	z3::expr eachExprToZ3(ref<Expr> &ele);
	z3::context& z3_ctx;
	std::vector<z3::expr> vecZ3Expr;
	std::vector<z3::expr> vecZ3ExprTest;
	std::vector<ref<Expr> > kqueryExprTest;
	void getFraction(double, Fraction&);
	int validNum(std::string& str);
public:
	KQuery2Z3(std::vector< ref<Expr> > &_queryExpr, z3::context& _z3_ctx);
	KQuery2Z3(z3::context& _z3_ctx);
	~KQuery2Z3();

	//only public function for call to complete convert kqueryExpr to z3Expr
	void getZ3Expr();
	z3::expr getZ3Expr(ref<Expr>& e);
	void printZ3AndKqueryExpr();
	void printKquery();
};

} /*namespace end*/


#endif /*end conditional inclusion*/
