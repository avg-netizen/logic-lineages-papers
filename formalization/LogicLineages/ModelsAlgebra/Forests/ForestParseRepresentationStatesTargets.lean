module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates.Targets
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationBinary ProfileAutomatonEncoding

def StateSetLeaf : Prop := ∀ M : Machine, stateSet M .atom = {M.leaf}

/-- All representations are considered, not just one chosen normal-form parse. -/
def StateSetGraphExact : Prop := ∀ (M : Machine) C, Reduced C → ∀ q,
  q ∈ stateSet M C ↔ ∃ t,
    Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C) ∧ machineRun M t = q

/-- Independent child representations and every binary association/permutation,
with every occurrence retained by a bijection, give exactly the full state subset. -/
def StateSetNodeExact : Prop := ∀ (M : Machine) o n (c : Fin (n + 2) → Cotree) q,
  q ∈ stateSet M (.node o n c) ↔
    ∃ (s : Shape (Fin (n + 2))) (v : Fin (n + 2) → M.State),
      Function.Bijective (label s) ∧ (∀ i, v i ∈ stateSet M (c i)) ∧
      CotreeGrammarShape.fold (M.node o) v s = q

/-- The full subset acceptance agrees exactly with the actual graph image. -/
def StateSetAcceptExact : Prop := ∀ (M : Machine) C, Reduced C →
  ((∃ q ∈ stateSet M C, M.accept q = true) ↔
    ∃ t, Nonempty (RankedParse.graph t ≃g ForestParseRepresentationCotree.graph C) ∧
      M.accept (machineRun M t) = true)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates.Targets
