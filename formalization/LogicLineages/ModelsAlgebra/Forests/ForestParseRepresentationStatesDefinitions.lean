module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShapeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationBinary ProfileAutomatonEncoding

/-- The source's full set S_M(C): all actual binary expansion states.
This semantic finite set does not itself claim an effective Parikh procedure. -/
noncomputable def stateSet (M : Machine) (C : Cotree) : Finset M.State := by
  classical
  exact Finset.univ.filter (fun q => ∃ t, Expansion t C ∧ machineRun M t = q)

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStates
