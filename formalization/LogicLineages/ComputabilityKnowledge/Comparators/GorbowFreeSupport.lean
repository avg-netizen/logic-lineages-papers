module

public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupport

@[expose] public section

/-! Source free-variable calibration, not a claim that ambient Formula n
already belongs to source L^n. Locality is valid for arbitrary extra symbols. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowFreeSupport
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowFreeSupport

def UnbindMembership : Prop := ∀ s i, i ∈ unbind s ↔ i + 1 ∈ s

def SupportBound : Prop :=
  (∀ (n : Nat) (t : Term n) (i : Nat), i ∈ termSupport t → i < n) ∧
  (∀ (n : Nat) (φ : Formula n) (i : Nat), i ∈ formulaSupport φ → i < n)

def UsesCalibration : Prop :=
  (∀ (n : Nat) (t : Term n) (i : Fin n), i.val ∈ termSupport t ↔ t.uses i = true) ∧
  (∀ (n : Nat) (φ : Formula n) (i : Fin n), i.val ∈ formulaSupport φ ↔ φ.uses i = true)

def ExactContext : Prop :=
  ∀ (n : Nat) (φ : Formula n), FreeNames (Finset.range n) φ ↔ ∀ i : Fin n, φ.uses i = true

def PreciseContext : Prop :=
  ∀ (n : Nat) (φ : Formula n), PreciselyFree n φ ↔ FreeNames (Finset.range n) φ

def SelectorCalibration : Prop :=
  (∀ φ : Formula 1, φ.uses 0 = true ↔ FreeNames {0} φ) ∧
  (∀ A : Selector, FreeNames {0} A.val)

def SemanticLocality : Prop :=
  (∀ (n : Nat) (t : Term n) (I : Interpretation) (v w : Fin n → Nat),
    (∀ i : Fin n, i.val ∈ termSupport t → v i = w i) → t.realize I v = t.realize I w) ∧
  (∀ (n : Nat) (φ : Formula n) (I : Interpretation) (v w : Fin n → Nat),
    (∀ i : Fin n, i.val ∈ formulaSupport φ → v i = w i) → (φ.realize I v ↔ φ.realize I w))

def Target : Prop := UnbindMembership ∧ SupportBound ∧ UsesCalibration ∧ ExactContext ∧
  PreciseContext ∧ SelectorCalibration ∧ SemanticLocality
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowFreeSupport
