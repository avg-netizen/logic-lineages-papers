module

public import LogicLineages.ComputabilityKnowledge.WWBoundedVectorPadding

@[expose] public section

/-! Exact semantic bounded-padding supplier, paper02 lines251–309. These
specific two vector comparisons encode V+1≤U. No undecidability/MRDP premise
or full cor:consumers assertion is included; uniform coding is a later gate. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorPadding

open PositiveExpression WWOrdinalTermSemantics WWGroundAdmissibility WWGroundClasses
open LogicLineages.ComputabilityKnowledge.WWBoundedVectorPadding

def OriginalHead : Prop :=
  ∀ (d : Nat) (u v : Expr (Fin d)), u.depth ≤ 2 → v.depth ≤ 2 →
    C d 0 (head u v) ∧ NormComparison true (embed (remainder u v)) (head u v)

def OriginalBoundedVectors : Prop :=
  ∀ (d : Nat) (u v : Expr (Fin d)), u.depth ≤ 2 → v.depth ≤ 2 →
    CVector (left u v) ∧ CVector (weakRight u v) ∧ CVector (strictRight u v) ∧
    VectorBoundedNorm (left u v) ∧ VectorBoundedNorm (weakRight u v) ∧ VectorBoundedNorm (strictRight u v)

def ExactComparisonReduction : Prop :=
  ∀ (d : Nat) (u v : Expr (Fin d)), u.depth ≤ 2 → v.depth ≤ 2 →
    (VectorLE (left u v) (weakRight u v) ↔ ∀ ρ : Fin d → PosNat, v.eval ρ + 1 ≤ u.eval ρ) ∧
    (VectorLT (left u v) (strictRight u v) ↔ ∀ ρ : Fin d → PosNat, v.eval ρ + 1 ≤ u.eval ρ)

def Target : Prop := OriginalHead ∧ OriginalBoundedVectors ∧ ExactComparisonReduction

end LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorPadding
