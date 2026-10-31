module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealFinite

def RunCalibration : Prop := ∀ (M : Machine) [DecidableEq M.State] t,
  machineRun (downwardMachine M) t = evaluate M t

def LanguageExact : Prop := ∀ (M : Machine) [DecidableEq M.State] t,
  (downwardMachine M).accept (machineRun (downwardMachine M) t) = true ↔
    ∃ u, Homeomorphic t u ∧ M.accept (machineRun M u) = true
end LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine.Targets
