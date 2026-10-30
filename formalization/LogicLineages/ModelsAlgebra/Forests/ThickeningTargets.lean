module

public import LogicLineages.ModelsAlgebra.Forests.ThickeningDefinitions

/-! Actual finite thickening obligations. The raw laws include n=0; leaf-count
preservation requires n>0 and includes empty template forests. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def ThickeningPartialOrderLaws : Prop :=
  ∀ (T : FiniteOrderForest) (n : Nat),
    (∀ x, thickLE T n x x) ∧
    (∀ x y z, thickLE T n x y → thickLE T n y z → thickLE T n x z) ∧
    (∀ x y, thickLE T n x y → thickLE T n y x → x = y)

def ThickeningPredecessorsChain : Prop :=
  ∀ (T : FiniteOrderForest) (n : Nat) (x y z : T.Carrier × Fin n),
    thickLE T n x z → thickLE T n y z → thickLE T n x y ∨ thickLE T n y x

def ThickeningMaximalPoints : Prop :=
  ∀ (T : FiniteOrderForest) (n : Nat) (x : T.Carrier × Fin n),
    (∀ y, thickLE T n x y → thickLE T n y x) ↔
      IsMax x.1 ∧ ∀ j : Fin n, j ≤ x.2

def ActualFiniteThickening : Prop :=
  ∀ (T : FiniteOrderForest) (n : Nat), 0 < n →
    ∃ (H : FiniteOrderForest) (points : (T.Carrier × Fin n) ≃ H.Carrier),
      (∀ x y, points x ≤ points y ↔ thickLE T n x y) ∧
      (leafFinset H.Carrier).card = (leafFinset T.Carrier).card

end LogicLineages.ModelsAlgebra.Forests.Targets
