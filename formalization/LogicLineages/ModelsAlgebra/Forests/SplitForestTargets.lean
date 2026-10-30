module

public import LogicLineages.ModelsAlgebra.Forests.SplitForestDefinitions

/-! Actual alternative finite source witness for paper03 thm:width.
This pays literal laminarity and constructs a real forest, not an assumed
binary-tree or root-preserving-embedding surrogate. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def SplitFamilyLaminar : Prop :=
  ∀ m : Nat, 4 ≤ m → IsLaminarLeafFamily (splitFamily m)

def ActualSplitForest : Prop :=
  ∀ m : Nat, 4 ≤ m → ∃ F : FiniteOrderForest,
    (leafFinset F.Carrier).card = m ∧
    ∃ u v : F.Carrier,
      Disjoint (finiteLeafCluster F u) (finiteLeafCluster F v) ∧
      2 ≤ (finiteLeafCluster F u).card ∧ 2 ≤ (finiteLeafCluster F v).card

end LogicLineages.ModelsAlgebra.Forests.Targets
