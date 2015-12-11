#ifndef EXPRCOSTCOMPUTER_H
#define EXPRCOSTCOMPUTER_H

#include <z3++.h>
#include <map>

class ExprCostComputer
{
private:
    std::map<const Z3_ast, int> exprCosts;
    z3::context* context;
    const int LINEAR_OP_COST = 1;
    const int MULTIPLICATION_OP_COST = 100;
    const int DIVISION_OP_COST = 150;

public:
    ExprCostComputer(z3::context&);

    int GetCost(const z3::expr&);
};

#endif // EXPRCOSTCOMPUTER_H
