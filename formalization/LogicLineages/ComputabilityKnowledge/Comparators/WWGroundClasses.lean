module

public import LogicLineages.ComputabilityKnowledge.WWGroundClasses

@[expose] public section

/-! Original ground-name C-class supplier for paper02, not a claim about
arbitrary higher-type source names, all finite-valued O, or hardness. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.WWGroundClasses

open PositiveExpression WWOrdinalTermSemantics WWClosedAssignment WWGroundAdmissibility
open LogicLineages.OrdinalComparison
open LogicLineages.ComputabilityKnowledge.WWGroundClasses

def SourceSubstitution : Prop :=
  ∀ (d i : Nat) (t : Term (Fin d)), C d i t →
    ∀ χ : Fin d → Term Empty, Admissible (support t) χ → B i (substitute χ t)

def GroundFinite : Prop :=
  ∀ (d : Nat) (t : Term (Fin d)), C d 0 t →
    ∀ χ : Fin d → Term Empty, Admissible (support t) χ →
      ∃ n : Nat, 0 < n ∧ closedValue (substitute χ t) = (n : Ordinal.{0})

def ExactGroundExtraction : Prop :=
  ∀ (d : Nat) (t : Term (Fin d)), C d 0 t →
    ∀ χ : Fin d → Term Empty, Admissible (support t) χ →
      0 < (closedValue (substitute χ t)).card.toNat ∧
      (((closedValue (substitute χ t)).card.toNat : Nat) : Ordinal.{0}) = closedValue (substitute χ t) ∧
      actualOrdinalNorm (closedValue (substitute χ t)) = (closedValue (substitute χ t)).card.toNat

def ExponentialFragmentMembership : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)) (i : Nat), 1 ≤ i → C d i (embed e)

def AdditiveFragmentMembership : Prop :=
  ∀ (d : Nat) (e : Expr (Fin d)), e.depth = 0 → C d 0 (embed e)

def Target : Prop := SourceSubstitution ∧ GroundFinite ∧ ExactGroundExtraction ∧
  ExponentialFragmentMembership ∧ AdditiveFragmentMembership

end LogicLineages.ComputabilityKnowledge.Comparators.WWGroundClasses
