module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCountsDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrencesDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts.Targets
open ForestParseRepresentationCotree ProfileAutomatonEncoding ForestParseRepresentationStates

def ChildCountExact : Prop := ∀ (M : Machine) [DecidableEq M.State] n (c : Fin n → Cotree) B,
  CotreeGrammar.counts (List.ofFn (fun i => stateSet M (c i))) B = childCounts M c B

/-- Exact source count-vector membership in the actual grammar's Parikh image.
No effective construction of a Presburger formula is asserted here. -/
def StateCountExact : Prop := ∀ (M : Machine) [DecidableEq M.State]
    o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet M (.node o n c) ↔
    ∃ w ∈ (CotreeGrammar.grammar (M.node o) q).language,
      ∀ B, CotreeGrammar.counts w B = childCounts M c B

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts.Targets
