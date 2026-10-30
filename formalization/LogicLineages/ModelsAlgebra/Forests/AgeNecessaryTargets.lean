module

public import LogicLineages.ModelsAlgebra.Forests.AgeDefinitions

/-! Necessity and cardinality clauses of paper03 prop:age. Existence for an
arbitrary nonempty hereditary JEP class remains a separate obligation. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open AgeConstruction

def RealizedForestAgeHasJEP : Prop :=
  ∀ (K : FiniteOrderForest → Prop) (A : CountableOrderForest),
    HasForestAge K A → ClassHasJEP K

def UnboundedForestAgeInfinite : Prop :=
  ∀ (K : FiniteOrderForest → Prop) (A : CountableOrderForest),
    HasForestAge K A → ClassUnbounded K → Infinite A.Carrier

def UnboundedForestAgeCountablyInfinite : Prop :=
  ∀ (K : FiniteOrderForest → Prop) (A : CountableOrderForest),
    HasForestAge K A → ClassUnbounded K → Nonempty (A.Carrier ≃ Nat)

end LogicLineages.ModelsAlgebra.Forests.Targets
