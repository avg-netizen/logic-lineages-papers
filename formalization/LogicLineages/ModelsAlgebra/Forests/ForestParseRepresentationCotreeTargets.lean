module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotreeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree.Targets
open RankedParse ForestParseRepresentationComponents

/-- Actual reduced cotree child fibers are the relevant graph/complement
connected pieces. No connected-fiber supplier is assumed here. -/
def ReducedComponents : Prop :=
  ∀ n (c : Fin (n + 2) → Cotree),
    (Reduced (.node .union n c) → ConnectedFibers (graph (.node .union n c)) Sigma.fst) ∧
    (Reduced (.node .join n c) → ConnectedFibers (graph (.node .join n c))ᶜ Sigma.fst)

/-- Exact graph-isomorphism uniqueness of genuine reduced unordered cotrees.
Existence by flattening and the complete binary representation/AC assertion
remain separate parts of the source lemma. -/
def ReducedUniqueness : Prop :=
  ∀ s t, Reduced s → Reduced t → Nonempty (graph s ≃g graph t) → StructuralIso s t

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotree.Targets
