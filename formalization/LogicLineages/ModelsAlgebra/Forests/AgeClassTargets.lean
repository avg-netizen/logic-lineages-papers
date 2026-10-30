module

public import LogicLineages.ModelsAlgebra.Forests.AgeModelDefinitions

/-! Transfer of actual forest classes to the literal order language. The final
relational realization is not yet asserted to be an order forest. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open FirstOrder AgeConstruction

def ForestModelClassNonempty : Prop :=
  ∀ K, ClassNonempty K → (ForestModelClass K).Nonempty

def ForestModelClassIsoInvariant : Prop :=
  ∀ K (M N : OrderModel), Nonempty (M ≃[Language.order] N) →
    (M ∈ ForestModelClass K ↔ N ∈ ForestModelClass K)

def ForestModelClassFinitelyGenerated : Prop :=
  ∀ K (M : OrderModel), M ∈ ForestModelClass K →
    Language.Structure.FG Language.order M

def ForestModelClassHereditary : Prop :=
  ∀ K, ClassHereditary K → Language.Hereditary (ForestModelClass K)

def ForestModelClassJointEmbedding : Prop :=
  ∀ K, ClassHasJEP K → Language.JointEmbedding (ForestModelClass K)

def ForestModelClassEssentiallyCountable : Prop :=
  ∀ K, (Quotient.mk' '' ForestModelClass K).Countable

def ForestClassCountableRelationalRealization : Prop :=
  ∀ K, ClassNonempty K → ClassHereditary K → ClassHasJEP K →
    ∃ M : OrderModel, Countable M ∧ Language.order.age M = ForestModelClass K

end LogicLineages.ModelsAlgebra.Forests.Targets
