module

public import LogicLineages.ModelsAlgebra.Forests.WidthAgeDefinitions

/-! Actual width-bounded countable ages; all finite and empty-carrier cases are
retained. No general forbidden-family decision algorithm is assumed. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open AgeConstruction

def WidthClassHereditary : Prop := ∀ m, ClassHereditary (WidthClass m)

def WidthClassNonempty : Prop := ∀ m, ClassNonempty (WidthClass m)

def WidthClassUnbounded : Prop := ∀ m, 1 ≤ m → ClassUnbounded (WidthClass m)

def RealizedWidthAgeWidth : Prop :=
  ∀ m A, HasForestAge (WidthClass m) A → WidthAtMost A.Carrier m

def WidthAgeClassification : Prop :=
  ∀ m, (∃ A : CountableOrderForest, HasForestAge (WidthClass m) A) ↔ m ≤ 3

def SmallWidthCountablyInfiniteAge : Prop :=
  ∀ m, 1 ≤ m → m ≤ 3 → ∃ A : CountableOrderForest,
    WidthAtMost A.Carrier m ∧ HasForestAge (WidthClass m) A ∧
      Nonempty (A.Carrier ≃ Nat)

end LogicLineages.ModelsAlgebra.Forests.Targets
