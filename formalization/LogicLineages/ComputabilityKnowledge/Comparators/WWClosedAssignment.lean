module

public import LogicLineages.ComputabilityKnowledge.WWClosedAssignment

@[expose] public section

/-! First original admissibility supplier. Exact original B0 positivity and
coverage, not a definition of B0 as positive naturals. Ground support-restricted
substitution/comparison correspondence is a subsequent separately checked gate. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.WWClosedAssignment

open LogicLineages.OrdinalComparison
open WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWClosedAssignment

def OriginalOrdinalClosure : Prop :=
  ∀ (ι : Type) (ρ : ι → Ordinal.{0}), (∀ i, ρ i < epsilonZero) →
    ∀ t : Term ι, denote ρ t < epsilonZero

def OriginalGroundValues : Prop :=
  ∀ t : Term Empty, B 0 t → ∃ n : Nat, 0 < n ∧ closedValue t = (n : Ordinal.{0})

def LiteralPositiveRepresentatives : Prop :=
  ∀ n : Nat, B 0 (positiveNumeral n) ∧ closedValue (positiveNumeral n) = ((n + 1 : Nat) : Ordinal.{0})

def SingletonBoundedNorm : Prop :=
  ∀ t : Term Empty, BoundedNorm [t]

def ExactFiniteExtraction : Prop :=
  ∀ t : Term Empty, B 0 t →
    0 < (closedValue t).card.toNat ∧
    (((closedValue t).card.toNat : Nat) : Ordinal.{0}) = closedValue t ∧
    actualOrdinalNorm (closedValue t) = (closedValue t).card.toNat

def Target : Prop := OriginalOrdinalClosure ∧ OriginalGroundValues ∧
  LiteralPositiveRepresentatives ∧ SingletonBoundedNorm ∧ ExactFiniteExtraction

end LogicLineages.ComputabilityKnowledge.Comparators.WWClosedAssignment
