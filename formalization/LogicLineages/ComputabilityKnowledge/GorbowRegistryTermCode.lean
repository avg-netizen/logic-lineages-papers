module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section
/-! Literal prefix builders for the arithmetic registry headers and restricted
arithmetic-term binders used by the actual atomic FS schema. No parsing,
semantic correctness or source-axiom membership is assumed by these builders. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCode
open GorbowCodeConstructors

def pairRaw (a b : List Nat) : List Nat := binary 3 (binary 4 (binary 3 a b) (binary 3 a b)) a

def tupleRaw (args : List (List Nat)) : List Nat :=
  args.foldr (fun a rest => unary 2 (pairRaw a rest)) [1]

def headerRaw (arity tag : Nat) (args : List (List Nat)) : List Nat :=
  pairRaw (numeral arity) (pairRaw (numeral tag) (tupleRaw args))

def evaluationRaw (raw : List Nat) : List Nat := unary 5 (headerRaw 1 1 [raw])

def arithmeticGuardRaw (raw : List Nat) : List Nat := unary 1 (headerRaw 1 2 [raw])

def closurePrefix : List Nat := [10,7] ++ arithmeticGuardRaw (variableCode 0)

def closeRaw (n : Nat) (raw : List Nat) : List Nat :=
  (List.replicate n closurePrefix).flatten ++ raw
end LogicLineages.ComputabilityKnowledge.GorbowRegistryTermCode
