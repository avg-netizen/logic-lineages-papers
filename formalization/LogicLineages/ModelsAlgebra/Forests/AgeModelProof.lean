module

public import LogicLineages.ModelsAlgebra.Forests.AgeModelTargets

/-! The order-language relation is exactly the original ≤, and reflected
relations pull actual finite forest orders back along arbitrary embeddings. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeModelProof

open FirstOrder AgeConstruction

theorem orderModelEmbeddingCalibration : Targets.OrderModelEmbeddingCalibration := by
  intro α β _ _
  constructor
  · rintro ⟨e⟩
    exact ⟨{
      toEmbedding := e.toEmbedding
      map_fun' := fun f => isEmptyElim f
      map_rel' := by
        intro n r v
        cases r
        exact e.le_iff_le }⟩
  · rintro ⟨e⟩
    refine ⟨{ toFun := e, inj' := e.injective, map_rel_iff' := ?_ }⟩
    intro x y
    exact e.map_rel .le ![x, y]

theorem orderModelIsoCalibration : Targets.OrderModelIsoCalibration := by
  intro α β _ _
  constructor
  · rintro ⟨e⟩
    exact ⟨{
      toEquiv := e.toEquiv
      map_fun' := fun f => isEmptyElim f
      map_rel' := by
        intro n r v
        cases r
        exact e.le_iff_le }⟩
  · rintro ⟨e⟩
    refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
    intro x y
    exact e.map_rel .le ![x, y]

theorem relationalFiniteForestPullback : Targets.RelationalFiniteForestPullback := by
  classical
  rintro M F ⟨e⟩
  let ef : M → F.Carrier := e
  letI : Finite M := Finite.of_injective ef e.injective
  letI : Fintype M := Fintype.ofFinite M
  letI : PartialOrder M := PartialOrder.lift ef e.injective
  let G : FiniteOrderForest := {
    Carrier := M
    carrierFintype := inferInstance
    carrierPartialOrder := inferInstance
    forest := fun {x y z} hx hy => F.forest hx hy }
  let eg : G.Carrier ↪o F.Carrier := {
    toFun := e
    inj' := e.injective
    map_rel_iff' := Iff.rfl }
  let iso : orderModel G.Carrier ≃[Language.order] M := {
    toEquiv := _root_.Equiv.refl M
    map_fun' := fun f => isEmptyElim f
    map_rel' := by
      intro n r v
      cases r
      exact (e.map_rel .le v).symm }
  exact ⟨G, ⟨eg⟩, ⟨iso⟩⟩

end LogicLineages.ModelsAlgebra.Forests.AgeModelProof
