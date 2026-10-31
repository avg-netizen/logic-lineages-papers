module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrencesDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesGrammar.Targets
open RankedParse ForestParseRepresentationCotree ProfileAutomatonEncoding ForestParseRepresentationStates

/-- Exact source grammar/child-count correspondence, prior to effective Parikh conversion.
A list permutation counts repeated child-state subsets with their full multiplicity. -/
def StateGrammarExact : Prop := ∀ (M : Machine) [DecidableEq M.State]
    o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet M (.node o n c) ↔
    ∃ w ∈ (CotreeGrammar.grammar (M.node o) q).language,
      w.Perm (List.ofFn (fun i => stateSet M (c i)))

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesGrammar.Targets
