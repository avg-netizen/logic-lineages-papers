module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealImageInclusionTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrderStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealImageInclusion.Proof
open RankedParse RankedIdealRegularCode RankedGraphImage RankedIdealCodeOrder ForestParseRepresentationFlatten
 private def witness : (t : Term) → RankedParse.Leaf t
  | .atom => ()
  | .node _ l _ => Sum.inl (witness l)
 theorem imageInclusionExact : Targets.ImageInclusionExact := by
  intro C D
  rw [RankedIdealCodeOrder.StatementChecks.inclusionExact C D]
  constructor
  · intro h G hG
    rcases hG with hempty | ⟨t,ht,⟨e⟩⟩
    · exact Or.inl hempty
    · obtain ⟨hred,⟨en⟩⟩ := ForestParseRepresentationFlatten.StatementChecks.binaryReducedRepresentation t
      obtain ⟨_,u,⟨eu⟩,hu⟩ := h (normalize t) ⟨hred,t,⟨en⟩,ht⟩
      exact Or.inr ⟨u,hu,⟨e.trans (en.trans eu.symm)⟩⟩
  · intro h T hT
    obtain ⟨hred,t,⟨et⟩,ht⟩ := hT
    have hi : Image (language C) (evalFinite t) :=
      Or.inr ⟨t,ht,⟨SimpleGraph.Iso.refl⟩⟩
    rcases h (evalFinite t) hi with hempty | ⟨u,hu,⟨eu⟩⟩
    · exact False.elim (hempty.false (witness t))
    · exact ⟨hred,u,⟨eu.symm.trans et⟩,hu⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealImageInclusion.Proof
