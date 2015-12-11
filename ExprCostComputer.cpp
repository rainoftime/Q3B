#include "ExprCostComputer.h"

using namespace z3;

ExprCostComputer::ExprCostComputer(z3::context &ctx)
{
    this->context = &ctx;
}

int ExprCostComputer::GetCost(const z3::expr &e)
{    
    auto item = exprCosts.find((Z3_ast)e);
    if (item != exprCosts.end())
    {
        return item->second;
    }

    if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();
      const std::string name = f.name().str();

      if (num == 0)
      {
        //e is an uninterpreted constant
        return 0;
      }
      else
      {
        int cost = 0;

        if (name == "bvadd" || name == "bvsub")
        {
            cost = LINEAR_OP_COST;
        }
        else if (name == "bvmul")
        {
            cost = MULTIPLICATION_OP_COST;
        }
        else if (name == "bvurem_i" || name == "bvudiv_i" || name == "bvsrem_i" || name == "bvsdiv_i")
        {
            cost = DIVISION_OP_COST;
        }

        for (unsigned i = 0; i < num; i++)
        {
          cost += GetCost(e.arg(i));
        }

        return cost;
      }
    }
    else if(e.is_quantifier())
    {
      return GetCost(e.body());
    }
    else
    {
        //e is var const
        return 0;
    }
}
