module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary.Targets
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationFlatten

/-- Soundness of actual ordered skeletons with bijective child-occurrence labels. -/
def ExpansionSound : Prop := ∀ t C, Expansion t C →
  Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C)

/-- Concrete flattening retains an actual association/permutation expansion certificate. -/
def NormalizationExpansion : Prop := ∀ t, Expansion t (normalize t)

/-- Reindexing unordered cotree children transports exact binary expansion certificates. -/
def ExpansionTransport : Prop := ∀ C D, StructuralIso C D →
  ∀ t, Expansion t C → Expansion t D

/-- Exact last clause of the source lemma, not a definition by graph isomorphism. -/
def BinaryCharacterization : Prop := ∀ t C, Reduced C →
  (Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C) ↔ Expansion t C)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinary.Targets
