module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth

@[expose] public section

/-! Actual source Var guards use sorted variable codes. Under the term binder,
v/formula/term indices are 2/1/0. UBF adds outer agent, so its inner agent index
is 3. Full closed-L terms and arithmetic-only UBF instances remain distinct. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruth
open GorbowSyntax GorbowRegistryTuple GorbowBooleanTruth

def variableGuard {n : Nat} (v : Term n) : Formula n := .universalRelation (headerTerm 1 3 [v])
def fullTermGuard {n : Nat} (t : Term n) : Formula n := .universalRelation (headerTerm 1 1 [t])
def arithmeticTermGuard {n : Nat} (t : Term n) : Formula n := .universalRelation (headerTerm 1 2 [t])
def namedGuard {n : Nat} (v φ : Term n) : Formula n := .universalRelation (headerTerm 2 0 [v,φ])
def allCodeTerm {n : Nat} (v φ : Term n) : Term n := .universalFunction (headerTerm 2 3 [v,φ])
def exCodeTerm {n : Nat} (v φ : Term n) : Term n := .universalFunction (headerTerm 2 4 [v,φ])
def instanceCodeTerm {n : Nat} (v φ t : Term n) : Term n := .universalFunction (headerTerm 3 0 [v,φ,t])

def forallAxiom : Sentence := .all (.all (.imp
  (.conj (variableGuard (.var 1)) (namedGuard (.var 1) (.var 0)))
  (biconditional (.truth (allCodeTerm (.var 1) (.var 0)))
    (.all (.imp (fullTermGuard (.var 0)) (.truth (instanceCodeTerm (.var 2) (.var 1) (.var 0))))))))
def existsAxiom : Sentence := .all (.all (.imp
  (.conj (variableGuard (.var 1)) (namedGuard (.var 1) (.var 0)))
  (biconditional (.truth (exCodeTerm (.var 1) (.var 0)))
    (.ex (.conj (fullTermGuard (.var 0)) (.truth (instanceCodeTerm (.var 2) (.var 1) (.var 0))))))))
def barcanAxiom : Sentence := .all (.all (.all (.imp
  (.conj (.agent (.var 2)) (.conj (variableGuard (.var 1)) (namedGuard (.var 1) (.var 0))))
  (.imp (.all (.imp (arithmeticTermGuard (.var 0)) (.knowledge (.var 3) (instanceCodeTerm (.var 2) (.var 1) (.var 0)))))
    (.knowledge (.var 2) (allCodeTerm (.var 1) (.var 0)))))))
end LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruth
