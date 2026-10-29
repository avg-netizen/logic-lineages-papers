module

public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration
public import Mathlib.Computability.RE

@[expose] public section

/-! Independent genuine computability and recursive-enumerability target.
REPred applies to source-defined counterexample predicates, not search-defined
surrogates. No AST Primcodable instance, MRDP premise or depth limit is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.FiniteComparisonEnumerationEffectivity

open LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration

def Target : Prop :=
  Computable (fun p : Nat × List Nat × List Nat => evalCode p.1 p.2.1 p.2.2) ∧
  Computable (fun p : List Nat × Nat => checkStrict p.1 p.2) ∧
  Computable (fun p : List Nat × Nat => checkWeak p.1 p.2) ∧
  REPred StrictCounterexample ∧ REPred WeakCounterexample

end LogicLineages.ComputabilityKnowledge.Comparators.FiniteComparisonEnumerationEffectivity
