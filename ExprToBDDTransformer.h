#ifndef ExprToBDDTransformer_h
#define ExprToBDDTransformer_h

#include <string>
#include <set>
#include <vector>
#include <map>
#include <unordered_map>
#include <bdd.h>
#include <bvec.h>
#include <fdd.h>
#include <z3++.h>
#include "ExprSimplifier.h"
#include "VariableOrderer.h"

typedef std::pair<std::string, int> var;

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };
enum ReorderType { NO_REORDER, WIN2, WIN2_ITE, WIN3, WIN3_ITE, SIFT, SIFT_ITE };
enum InitialOrder { INTERLEAVE_ALL, HEURISTIC, SEQUENTIAL };

typedef std::pair<std::string, BoundType> boundVar;

class ExprToBDDTransformer
{
  private:
    std::map<std::string, bvec> vars;
    std::map<std::string, bdd> varSets;
    std::map<std::string, std::vector<int>> varIndices;

    std::set<var> constSet;
    std::set<var> boundVarSet;

    std::map<const Z3_ast, std::pair<bdd, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<bvec, std::vector<boundVar>>> bvecExprCache;

    std::set<Z3_ast> processedVarsCache;

    bdd m_bdd;

    z3::context* context;
    //std::map<std::string, int> varToBddIndex;

    z3::expr expression;
    int bv_size = 16;

    void getVars(const z3::expr &e);
    void loadVars();    
    
    void loadBDDsFromExpr(z3::expr);
    bdd getBDDFromExpr(const z3::expr&, std::vector<boundVar>, bool onlyExistentials = false);
    bvec getBvecFromExpr(const z3::expr&, std::vector<boundVar>);

    unsigned int getNumeralValue(const z3::expr&);
    unsigned int getNumeralOnes(const z3::expr&);	
    bvec getNumeralBvec(const z3::expr&);

    bdd getConjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&);
    bdd getDisjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&);

    int exisentialBitWidth;
    int universalBitWidth;
    ApproximationType approximationType;
    ReorderType reorderType = NO_REORDER;
    InitialOrder initialOrder = HEURISTIC;
	bool m_negateMul;

    int cacheHits = 0;

  public:
    ExprToBDDTransformer(z3::context& context, z3::expr e) : ExprToBDDTransformer(context, e, HEURISTIC) {}
    ExprToBDDTransformer(z3::context& context, z3::expr e, InitialOrder initialOrder);
    bdd Proccess();

    bdd ProcessUnderapproximation(int);
    bdd ProcessOverapproximation(int);

    std::map<std::string, bdd> GetVarSets() { return varSets; }       

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }

	void SetNegateMul(bool negateMul)
	{
		m_negateMul = negateMul;
	}

    void setReorderType(ReorderType rt)
    {
        reorderType = rt;

        if (reorderType != NO_REORDER)
        {
          bdd_varblockall();

          switch (reorderType)
          {
              case WIN2:
                  bdd_autoreorder(BDD_REORDER_WIN2);
                  break;
              case WIN2_ITE:
                  bdd_autoreorder(BDD_REORDER_WIN2ITE);
                  break;
              case WIN3:
                  bdd_autoreorder(BDD_REORDER_WIN3);
                  break;
              case WIN3_ITE:
                  bdd_autoreorder(BDD_REORDER_WIN3ITE);
                  break;
              case SIFT:
                  bdd_autoreorder(BDD_REORDER_SIFT);
                  break;
              case SIFT_ITE:
                  bdd_autoreorder(BDD_REORDER_SIFTITE);
                  break;
              default:
                  break;
          }
        }
    }
};

#endif
