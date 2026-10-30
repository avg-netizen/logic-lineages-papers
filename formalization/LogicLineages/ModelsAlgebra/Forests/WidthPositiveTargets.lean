module

public import LogicLineages.ModelsAlgebra.Forests.WidthJEPDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessDefinitions

/-! Actual common-host construction and full source classification for paper03
thm:width. The shared template and all calibrated maps are existentially proved,
not supplied as final hypotheses. Width zero is recorded separately as in the
source's empty-forest convention. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def SmallWidthTemplateCalibration : Prop :=
  ∀ m : Nat, 0 < m → m ≤ 3 →
    ∃ T : FiniteOrderForest, (leafFinset T.Carrier).card = m ∧
      ∀ F : FiniteOrderForest, WidthAtMost F.Carrier m →
        ∃ q : F.Carrier → T.Carrier,
          (∀ x y, q x ≤ q y ↔ finiteLeafCluster F y ⊆ finiteLeafCluster F x) ∧
          ∀ x y, q x = q y ↔ finiteLeafCluster F x = finiteLeafCluster F y

def WidthZeroHasJEP : Prop := WidthHasJEP 0

def WidthAtMostThreeHasJEP : Prop :=
  ∀ m : Nat, m ≤ 3 → WidthHasJEP m

/-- Exactly the numbered source theorem, with no missing positive supplier. -/
def FullWidthJEPClassification : Prop :=
  ∀ m : Nat, 1 ≤ m → (WidthHasJEP m ↔ m ≤ 3)

end LogicLineages.ModelsAlgebra.Forests.Targets
