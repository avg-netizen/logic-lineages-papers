module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryDefinitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalTargets
open Elementary

/-- Transport of the exact natural-input normalizer to arbitrary finite
parameter types. Parameters and existential wire valuations remain natural. -/
def FiniteParameterNormalization : Prop :=
  ∀ (α : Type) [Fintype α] (S : Set (α → Nat)), Dioph S ↔ Represents S

/-- The length is an input coordinate, not a fixed numeral. All original
parameter values and the empty initial interval are retained. -/
def LengthBoundedUniversalClosure : Prop :=
  ∀ (n : Nat) (R : Nat → (Fin n → Nat) → Prop),
    Dioph {w : Option (Fin n) → Nat | R (w none) (w ∘ some)} →
    Dioph {w : Option (Fin n) → Nat | ∀ i, i < w none → R i (w ∘ some)}

-- The final comparator is the unchanged
-- CipherTargets.VariableBoundedUniversalClosure, not a replacement definition.
end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalTargets
