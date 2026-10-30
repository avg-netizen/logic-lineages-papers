module

public import LogicLineages.ComputabilityKnowledge.GorbowStandardInduction

@[expose] public section

/-! Literal PA(L) induction realization in every standard natural-number
expansion, as used in paper12 consistency. Context is ambient, not exact-free
source arity; unused parameters are permitted and universally closed. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowStandardInduction

open GorbowSyntax GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowStandardInduction

def SuccessorSemantics : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (I : Interpretation) (v : Fin n → Nat) (x : Nat),
    (successorInstance φ).realize I (Fin.cases x v) ↔ φ.realize I (Fin.cases (x + 1) v)

def BaseSemantics : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (I : Interpretation) (v : Fin n → Nat),
    (instantiate φ .zero).realize I v ↔ φ.realize I (Fin.cases 0 v)

def OpenInductionRealized : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (I : Interpretation) (v : Fin n → Nat),
    (inductionAxiom φ).realize I v

def UniversalClosureSemantics : Prop :=
  ∀ (n : Nat) (φ : Formula n) (I : Interpretation),
    (universalClosure φ).realize I Fin.elim0 ↔ ∀ v : Fin n → Nat, φ.realize I v

def ClosedInductionRealized : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (I : Interpretation), (closedInductionAxiom φ).realize I Fin.elim0

def Target : Prop := SuccessorSemantics ∧ BaseSemantics ∧ OpenInductionRealized ∧
  UniversalClosureSemantics ∧ ClosedInductionRealized

end LogicLineages.ComputabilityKnowledge.Comparators.GorbowStandardInduction
