module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion.Targets
open RankedParse ProfileAutomatonEncoding

def ProductiveExact : Prop := ∀ (M : Machine) [DecidableEq M.State] q,
  q ∈ productive M ↔ ∃ t, machineRun M t = q

def RunExact : Prop := ∀ (M : Machine) [DecidableEq M.State] t q,
  Run M t q ↔ ∃ u, Homeomorphic t u ∧ machineRun M u = q

def AcceptanceExact : Prop := ∀ (M : Machine) [DecidableEq M.State] t,
  Accepts M t ↔ ∃ u, Homeomorphic t u ∧ M.accept (machineRun M u) = true

def RunProductive : Prop := ∀ (M : Machine) [DecidableEq M.State] t q,
  Run M t q → q ∈ productive M
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion.Targets
