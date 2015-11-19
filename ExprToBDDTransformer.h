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

typedef std::pair<std::string, BoundType> boundVar;

class ExprToBDDTransformer
{
  template<class T>
  struct CacheItem
  {
    public:
      T cachedValue;
      std::vector<boundVar> boundVars;
      bdd mustSatisfy;
      bdd alreadySatisfies;

      CacheItem(T cachedValue) : cachedValue(cachedValue)
      {
          boundVars = std::vector<boundVar>();
          mustSatisfy = bdd_true();
          alreadySatisfies = bdd_false();
      }

      CacheItem(T cachedValue, std::vector<boundVar> boundVars) : cachedValue(cachedValue), boundVars(boundVars)
      {
          mustSatisfy = bdd_true();
          alreadySatisfies = bdd_false();
      }

      CacheItem(T cachedValue, std::vector<boundVar> boundVars, bdd mustSatisfy, bdd alreadySatisfies) :
          cachedValue(cachedValue), boundVars(boundVars), mustSatisfy(mustSatisfy), alreadySatisfies(alreadySatisfies)
      {
      }
  };

  private:
    std::map<std::string, bvec> vars;
    std::map<std::string, bdd> varSets;
    std::map<std::string, std::vector<int>> varIndices;

    std::set<var> constSet;
    std::set<var> boundVarSet;

    std::map<const Z3_ast, CacheItem<bdd>> bddExprCache;
    std::map<const Z3_ast, CacheItem<bvec>> bvecExprCache;

    std::set<Z3_ast> processedVarsCache;

    bdd m_bdd;

    z3::context* context;
    //std::map<std::string, int> varToBddIndex;

    z3::expr expression;
    int bv_size = 16;

    void getVars(const z3::expr &e);
    void loadVars();    
    
    void loadBDDsFromExpr(z3::expr);
    bdd getBDDFromExpr(const z3::expr&, std::vector<boundVar>, bdd mustSatisfy = bdd_true(), bdd alreadySatisfies = bdd_false());
    bvec getBvecFromExpr(const z3::expr&, std::vector<boundVar>, bdd mustSatisfy = bdd_true(), bdd alreadySatisfies = bdd_false(), bool propagateVars = false);

    unsigned int getNumeralValue(const z3::expr&);
    bvec getNumeralBvec(const z3::expr&);
    bvec getVariableBvec(const std::string&, bdd, bdd, bool);

    bdd getConjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bdd mustSatisfy = bdd_true(), bdd alreadySatisfies = bdd_false());
    bdd getDisjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bdd mustSatisfy = bdd_true(), bdd alreadySatisfies = bdd_false());

    int exisentialBitWidth;
    int universalBitWidth;
    ApproximationType approximationType;

  public:
    ExprToBDDTransformer(z3::context&, z3::expr);
    bdd Proccess();

    bdd ProcessUnderapproximation(int);
    bdd ProcessOverapproximation(int);

    std::map<std::string, bdd> GetVarSets() { return varSets; }       

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }
};

#endif
