module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesDefinitions
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Count
public import Mathlib.Data.Fintype.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts
open ForestParseRepresentationCotree ProfileAutomatonEncoding ForestParseRepresentationStates

/-- The manuscript's exact count c_B, with actual child occurrences indexed by Fin. -/
noncomputable def childCounts (M : Machine) {n : Nat} (c : Fin n → Cotree)
    (B : Finset M.State) : Nat := by
  classical
  exact (Finset.univ.filter (fun i => stateSet M (c i) = B)).card

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCounts
