module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.Targets
open ForestParseRepresentationCotree ForestParseRepresentationBinary

/-- Whole repaired `lem:canonical-cotree`: existence, uniqueness up to the
actual unordered cotree isomorphism, and the complete independent binary
association/permutation characterization. A graph with a union/join
representation is represented by the arbitrary input parse `t`. -/
def FullCanonicalCotree : Prop :=
  ∀ t : RankedParse.Term, ∃ C : Cotree,
    Reduced C ∧
    Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C) ∧
    (∀ D, Reduced D →
      Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph D) →
      StructuralIso C D) ∧
    (∀ s : RankedParse.Term,
      Nonempty (RankedParse.graph s ≃g ForestParseRepresentationCotree.graph C) ↔
        Expansion s C)

end LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.Targets
