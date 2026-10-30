module

public import LogicLineages.ModelsAlgebra.Forests.LaminarForestDefinitions

/-! Actual finite forest realization of literal laminar families for the width
witnesses of paper 03. Empty finite leaf types/families are included in the
laminar case; the binary case's nonempty convention is inherited explicitly. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

noncomputable def BinaryClusterRelabeling : Prop := by
  classical
  exact ∀ (α β : Type) (L : Finset α) (family : Finset (Finset α)) (e : α ↪ β),
    IsBinaryClusterFamily L family →
      IsBinaryClusterFamily (L.map e) (family.image (fun B => B.map e))

noncomputable def LaminarFamilyForestRepresentation : Prop := by
  classical
  exact ∀ (α : Type) [Fintype α] (family : Finset (Finset α)),
    IsLaminarLeafFamily family →
    ∃ (F : FiniteOrderForest) (nodes : family ≃ F.Carrier) (leaves : α ≃ ForestLeaf F),
      (∀ B C : family, nodes B ≤ nodes C ↔ C.val ⊆ B.val) ∧
      (∀ (B : family) (a : α), nodes B ≤ (leaves a).val ↔ a ∈ B.val) ∧
      ∀ a : α, (nodes.symm (leaves a).val).val = {a}

noncomputable def BinaryFamilyForestRepresentation : Prop := by
  classical
  exact ∀ (α : Type) [Fintype α] (family : Finset (Finset α)),
    IsBinaryClusterFamily Finset.univ family →
    ∃ (F : FiniteOrderForest) (nodes : family ≃ F.Carrier) (leaves : α ≃ ForestLeaf F),
      (∀ B C : family, nodes B ≤ nodes C ↔ C.val ⊆ B.val) ∧
      (∀ (B : family) (a : α), nodes B ≤ (leaves a).val ↔ a ∈ B.val) ∧
      (∀ a : α, (nodes.symm (leaves a).val).val = {a}) ∧ HasBinaryLeafClusters F

end LogicLineages.ModelsAlgebra.Forests.Targets
