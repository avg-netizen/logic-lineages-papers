module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealContext.Proof
open RankedParse

theorem embeddingReflexive : Targets.EmbeddingReflexive := by
  intro t
  induction t with
  | atom => exact .atom
  | node o l r hl hr => exact .couple o hl hr

theorem embeddingTransitive : Targets.EmbeddingTransitive := by
  intro s t u hst htu
  induction htu generalizing s with
  | atom => exact hst
  | left o h ih => exact .left o (ih hst)
  | right o h ih => exact .right o (ih hst)
  | couple o hl hr ihl ihr =>
      cases hst with
      | left _ h => exact .left o (ihl h)
      | right _ h => exact .right o (ihr h)
      | couple _ h₁ h₂ => exact .couple o (ihl h₁) (ihr h₂)

theorem plugMonotone : Targets.PlugMonotone := by
  intro c s t h
  induction c with
  | hole => exact h
  | left o c r ih => exact .couple o ih (embeddingReflexive r)
  | right o l c ih => exact .couple o (embeddingReflexive l) ih

theorem holeEmbeds : Targets.HoleEmbeds := by
  intro c t
  induction c with
  | hole => exact embeddingReflexive t
  | left o c r ih => exact .left o ih
  | right o l c ih => exact .right o ih

theorem plugComposition : Targets.PlugComposition := by
  intro c d t
  induction c with
  | hole => rfl
  | left o c r ih => simp only [compose, plug, ih]
  | right o l c ih => simp only [compose, plug, ih]
end LogicLineages.ModelsAlgebra.Forests.RankedIdealContext.Proof
