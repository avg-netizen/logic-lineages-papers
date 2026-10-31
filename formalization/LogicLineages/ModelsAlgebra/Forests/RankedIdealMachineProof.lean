module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealFinite

theorem runCalibration : Targets.RunCalibration := by
  intro M _ t
  induction t with
  | atom => rfl
  | node o l r ihl ihr =>
      change close M (nodeSeeds M o (machineRun (downwardMachine M) l)
        (machineRun (downwardMachine M) r)) = _
      rw [ihl, ihr]
      rfl

theorem languageExact : Targets.LanguageExact := by
  intro M _ t
  rw [runCalibration M t]
  exact RankedIdealFinite.StatementChecks.acceptanceExact M t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine.Proof
