module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularStateTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealRegular RankedIdealComponents RankedGraphImage

private theorem calibration (M : Machine) [DecidableEq M.State] q t :
    machineRun (stateMachine M q) t = RankedIdealFinite.evaluate M t := by
  induction t with
  | atom => rfl
  | node o l r ihl ihr =>
      change (stateMachine M q).node o (machineRun (stateMachine M q) l)
        (machineRun (stateMachine M q) r) = _
      rw [ihl, ihr]
      rfl

theorem stateLanguageExact : Targets.StateLanguageExact := by
  intro M _ q t
  change decide (q ∈ (show Finset M.State from machineRun (stateMachine M q) t)) = true ↔ _
  rw [calibration M q t, decide_eq_true_eq]
  exact RankedIdealFinite.StatementChecks.evaluationExact M t q

theorem compiledNonlinearIdeal : Targets.CompiledNonlinearIdeal := by
  intro M _ q hq
  have he : language (stateMachine M q) = stateLanguage M q :=
    funext (fun t => propext (stateLanguageExact M q t))
  rw [he]
  exact RankedIdealComponents.StatementChecks.nonlinearIdeal M q hq
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState.Proof
