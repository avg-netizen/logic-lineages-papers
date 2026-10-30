module

public import LogicLineages.ModelsAlgebra.Forests.CombForestDefinitions

/-! Relabeling actual source forest leaves into the small comb templates.
All small finite forest classes, including width zero/empty carriers, occur.
No order embedding or template correctness is assumed in these targets. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

noncomputable def LaminarLeafEquivRelabeling : Prop := by
  classical
  exact ∀ (α β : Type) (family : Finset (Finset α)) (e : α ≃ β),
    IsLaminarLeafFamily family →
      IsLaminarLeafFamily (family.image (fun B => B.map e.toEmbedding))

noncomputable def SmallForestLeafLabeling : Prop := by
  classical
  exact ∀ (F : FiniteOrderForest) (m : Nat), m ≤ 3 → WidthAtMost F.Carrier m →
    ∃ e : ForestLeaf F ↪ Fin m, ∀ v : F.Carrier,
      (finiteLeafCluster F v).map e ∈ combFamily m

end LogicLineages.ModelsAlgebra.Forests.Targets
