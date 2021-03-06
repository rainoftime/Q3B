#ifndef BDDSOLVER_H
#define BDDSOLVER_H

#include <z3++.h>
#include <bdd.h>
#include "ExprToBDDTransformer.h"

enum Result { SAT, UNSAT, UNKNOWN };
enum Approximation { UNDERAPPROXIMATION, OVERAPPROXIMATION, NO_APPROXIMATION };

class Solver
{
public:
    Solver() : m_approximationType(NO_APPROXIMATION), m_effectiveBitWidth(0) { }
    Solver(bool propagateUncoinstrained) :
    	m_approximationType(NO_APPROXIMATION), m_effectiveBitWidth(0), m_propagateUncoinstrained(propagateUncoinstrained), m_negateMul(false), m_initialOrder(HEURISTIC) { }
    Result GetResult(z3::expr);

    void SetApproximation(Approximation approximation, int bitWidth)
    {
        m_approximationType = approximation;
        m_effectiveBitWidth = bitWidth;
    }

    void SetReorderType(ReorderType reorderType)
    {
        m_reorderType = reorderType;
    }

    void SetInitialOrder(InitialOrder initialOrder)
    {
        m_initialOrder = initialOrder;
    }

    void SetNegateMul(bool negateMul)
    {
		m_negateMul = negateMul;
    }	

private:
    Approximation m_approximationType;
    int m_effectiveBitWidth;
    bool m_propagateUncoinstrained;
	bool m_negateMul;
    ReorderType m_reorderType;
    InitialOrder m_initialOrder;

    void set_bdd();

    Result runUnderApproximation(ExprToBDDTransformer&, int);
    Result runOverApproximation(ExprToBDDTransformer&, int);

    Result runWithOverApproximations(ExprToBDDTransformer&);
    Result runWithUnderApproximations(ExprToBDDTransformer&);
};

#endif // BDDSOLVER_H
