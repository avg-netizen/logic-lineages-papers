module

public import LogicLineages.ComputabilityKnowledge.WWGroundAdmissibility

@[expose] public section

/-! Original admissible source domain, not comparison restricted by an
unproved numerical encoding. Literal restriction/extension and locality pay
the exact occurring-variable domain of source Definition 2.7, including d=0.
Only embedded positive exponential expressions are transported. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.WWGroundAdmissibility

open PositiveExpression WWOrdinalTermSemantics WWClosedAssignment
open LogicLineages.ComputabilityKnowledge.WWGroundAdmissibility

def OriginalLocality : Prop :=
  ∀ (d : Nat) (a : Term (Fin d)) (ρ σ : Fin d → Ordinal.{0}),
    (∀ i ∈ support a, ρ i = σ i) → denote ρ a = denote σ a

def RestrictionExtension : Prop :=
  ∀ (d : Nat) (S : Finset (Fin d)) (χ : Fin d → Term Empty),
    Admissible S χ →
      Admissible Finset.univ (fun i => if i ∈ S then χ i else Term.one) ∧
      (∀ i ∈ S, (if i ∈ S then χ i else Term.one) = χ i)

def ExactPositiveTuples : Prop :=
  (∀ (d : Nat) (S : Finset (Fin d)) (χ : Fin d → Term Empty),
    Admissible S χ → ∃ ρ : Fin d → PosNat,
      ∀ i ∈ S, closedValue (χ i) = ((ρ i : Nat) : Ordinal.{0})) ∧
  (∀ (d : Nat) (ρ : Fin d → PosNat), ∃ χ : Fin d → Term Empty,
    Admissible Finset.univ χ ∧ ∀ i, closedValue (χ i) = ((ρ i : Nat) : Ordinal.{0}))

def SourceComparisons : Prop :=
  ∀ (d : Nat) (a b : Expr (Fin d)) (weak : Bool),
    Comparison weak (embed a) (embed b) ↔
      ∀ ρ : Fin d → PosNat, if weak then a.eval ρ ≤ b.eval ρ else a.eval ρ < b.eval ρ

def SourceEquality : Prop :=
  ∀ (d : Nat) (a b : Expr (Fin d)),
    Equality (embed a) (embed b) ↔ ∀ ρ : Fin d → PosNat, a.eval ρ = b.eval ρ

def SourceNormComparisons : Prop :=
  ∀ (d : Nat) (a b : Expr (Fin d)) (weak : Bool),
    NormComparison weak (embed a) (embed b) ↔
      ∀ ρ : Fin d → PosNat, if weak then a.eval ρ ≤ b.eval ρ else a.eval ρ < b.eval ρ

def Target : Prop := OriginalLocality ∧ RestrictionExtension ∧ ExactPositiveTuples ∧
  SourceComparisons ∧ SourceEquality ∧ SourceNormComparisons

end LogicLineages.ComputabilityKnowledge.Comparators.WWGroundAdmissibility
