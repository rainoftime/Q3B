#ifndef UNCONSTRAINEDVARIABLESIMPLIFIER_H
#define UNCONSTRAINEDVARIABLESIMPLIFIER_H

#include "z3++.h"
#include <unordered_map>
#include <map>
#include <vector>
#include <string>
#include <tuple>

enum BoundType { EXISTENTIAL, UNIVERSAL };

class UnconstrainedVariableSimplifier
{
public:
    UnconstrainedVariableSimplifier(z3::context &ctx, z3::expr expr) : expression(expr)
    {
      this->context = &ctx;

      countVariableOccurences(expression, std::vector<std::string>());
    }

    void PrintUnconstrained()
    {
        bool allConstrained = true;
		
        for (auto &item : variableCounts)
        {
            std::cout << "var " << item.first << " - " << item.second << " times" << std::endl;

            if (item.second == 1)
            {
                allConstrained = false;
                //std::cout << "Unconstrained variable: " << item.first << std::endl;
            }
        }
        if (allConstrained) std::cout << "All variables constrained" << std::endl;
    }

    void SimplifyOnce()
    {
        expression = simplifyOnce(expression, {}, true);
    }

    z3::expr GetExpr() const { return expression; }

    void SimplifyIte();

private:
    z3::context* context;
    z3::expr expression;

    //std::map<const Z3_ast, std::pair<std::unordered_map<std::string, int>, std::vector<std::string>>> subformulaVariableCounts;
    std::unordered_map<const z3::expr*, int> subformulaMaxDeBruijnIndices;
    std::unordered_map<std::string, int> variableCounts;

    typedef std::pair<std::string, BoundType> boundVar;
    typedef std::map<const Z3_ast, std::pair<z3::expr, const std::vector<boundVar>>> cacheMapType;

    cacheMapType trueSimplificationCache;
    cacheMapType falseSimplificationCache;

    int countVariableOccurences(z3::expr, std::vector<std::string>);
	void addVariableOccurence(const std::string&);

    z3::expr simplifyOnce(const z3::expr, std::vector<std::pair<std::string, BoundType>>, bool);
    bool isUnconstrained(const z3::expr, const std::vector<std::pair<std::string, BoundType>>&);
    bool isVar(const z3::expr&);
    bool isBefore(const z3::expr&, const z3::expr&);
    BoundType getBoundType(const z3::expr&, const std::vector<std::pair<std::string, BoundType>>&);

	int getNumberOfLeadingZeroes(const z3::expr&);
};

#endif // UNCONSTRAINEDVARIABLESIMPLIFIER_H
