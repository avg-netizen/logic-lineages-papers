module

public import LogicLineages.ComputabilityKnowledge.GorbowPACore

@[expose] public section
/-! Actual first-order proof trees over literal additional closed axioms.
The parameter is an external set of sentences, not a provability predicate
or an asserted presentation of Base/DCB. Arithmetic remains the paid PA(L)
core, and all semantic conclusions concern standard-N interpretations. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryProof
open GorbowSyntax GorbowPACore

def weakenClosed (n : Nat) (σ : Sentence) : Formula n :=
  GorbowFormulaSubstitution.substituteFormula (Fin.elim0 : Fin 0 → Term n) σ

inductive Derivation (A : Sentence → Prop) : {n : Nat} → Formula n → Type
  | logical {n} (w : LogicalInstance n) : Derivation A (logicalFormula w)
  | arithmetic {n} (w : ArithmeticInstance n) : Derivation A (arithmeticFormula w)
  | axiom {n} (σ : Sentence) : A σ → Derivation A (weakenClosed n σ)
  | mp {n} {a b : Formula n} : Derivation A (.imp a b) → Derivation A a → Derivation A b
  | generalize {n} {a : Formula (n+1)} : Derivation A a → Derivation A (.all a)

def usedAxioms {A : Sentence → Prop} : {n : Nat} → {φ : Formula n} → Derivation A φ → List Sentence
  | _,_,.logical _ => []
  | _,_,.arithmetic _ => []
  | _,_,.axiom σ _ => [σ]
  | _,_,.mp p q => usedAxioms p ++ usedAxioms q
  | _,_,.generalize p => usedAxioms p
end LogicLineages.ComputabilityKnowledge.GorbowTheoryProof
