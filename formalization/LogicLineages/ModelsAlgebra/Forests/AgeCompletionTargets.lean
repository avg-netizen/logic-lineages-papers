module

public import LogicLineages.ModelsAlgebra.Forests.AgeModelDefinitions

/-! Full paper03 prop:age: literal finite/countable forest realization of every
nonempty hereditary JEP class, with countable infinity for unbounded sizes. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open FirstOrder AgeConstruction

def ActualForestModelAgeCalibration : Prop :=
  ∀ K (A : CountableOrderForest), ClassHereditary K →
    Language.order.age (orderModel A.Carrier) = ForestModelClass K →
    HasForestAge K A

def FullForestAgeRealization : Prop :=
  ∀ K, ClassNonempty K → ClassHereditary K →
    ((∃ A : CountableOrderForest, HasForestAge K A) ↔ ClassHasJEP K)

def UnboundedForestAgeRealization : Prop :=
  ∀ K, ClassNonempty K → ClassHereditary K → ClassHasJEP K → ClassUnbounded K →
    ∃ A : CountableOrderForest,
      HasForestAge K A ∧ Nonempty (A.Carrier ≃ Nat)

end LogicLineages.ModelsAlgebra.Forests.Targets
