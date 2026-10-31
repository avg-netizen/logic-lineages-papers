module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten.Targets
open RankedParse ForestParseRepresentationCotree

/-- Concrete same-operation flatten/merge preserves the actual sum/join graph
and retains reducedness, never silently deleting or duplicating occurrences. -/
def MergeCorrect : Prop :=
  ∀ o s t, Reduced s → Reduced t →
    Reduced (merge o s t) ∧
    Nonempty (operationGraph o (ForestParseRepresentationCotree.graph s)
      (ForestParseRepresentationCotree.graph t) ≃g ForestParseRepresentationCotree.graph (merge o s t))

/-- Every actual binary parse has a concretely constructed reduced cotree
with the same leaf graph. This proves source existence/flattening, not yet
all possible binary association/permutation reconstructions. -/
def BinaryReducedRepresentation : Prop :=
  ∀ t, Reduced (normalize t) ∧
    Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph (normalize t))

/-- The normalization is canonical up to the literal unordered cotree isomorphism. -/
def NormalizationCanonical : Prop :=
  ∀ s t, Nonempty (RankedParse.graph s ≃g RankedParse.graph t) →
    StructuralIso (normalize s) (normalize t)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten.Targets
