module
public import LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletionTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlattenProof
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryProof

@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.Proof
open ForestParseRepresentationCotree ForestParseRepresentationFlatten

theorem fullCanonicalCotree : Targets.FullCanonicalCotree := by
  intro t
  obtain ⟨hred, ⟨e⟩⟩ := ForestParseRepresentationFlatten.Proof.binaryReducedRepresentation t
  refine ⟨normalize t, hred, ⟨e⟩, ?_, ?_⟩
  · intro D hD hgraph
    obtain ⟨f⟩ := hgraph
    exact ForestParseRepresentationCotree.Proof.reducedUniqueness
      (normalize t) D hred hD ⟨e.symm.trans f⟩
  · intro s
    exact ForestParseRepresentationBinary.Proof.binaryCharacterization s (normalize t) hred

end LogicLineages.ModelsAlgebra.Forests.CanonicalCotreeCompletion.Proof
