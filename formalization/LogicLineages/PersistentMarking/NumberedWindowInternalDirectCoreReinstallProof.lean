module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericProof
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowFormulaCalibrationChecks (exact_InterpretsEvaluatingPrograms)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectCoreNumericProof (exact_NumericDCore)
open NumberedWindowInternalDirectCoreReinstallTargets

theorem exact_Reinstall : ExactReinstall := by
  intro xs s i j r count h hf
  let d := dCore i r count
  let p := data i j r d
  have he : Evaluates (checks xs s) i j r d := by
    refine ⟨h.1,h.2.1,h.2.2,?_⟩
    intro src cert dst
    change evaluate (dCore i r count) (src ::ᵥ cert ::ᵥ dst ::ᵥ nil) =
      (NumberedWindowDirectAlgorithm.direct (checks xs s).scalar (checks xs s).positive src cert dst).toNat
    exact exact_NumericDCore i r count (checks xs s).scalar (checks xs s).positive h.1 h.2.2 hf src cert dst
  change Evaluates (checks xs s) i j r d ∧
    NumberedWindowFormulaCalibrationTargets.Interprets (checks xs s) p ∧
    NumberedWindowInternalAccessibilityTargets.Rules p
  exact ⟨he, exact_InterpretsEvaluatingPrograms (checks xs s) i j r d he,
    ⟨actualOriginalMembershipEquation p, actualOriginalCarrierExtraction p,
      actualOriginalSuccessorClosure p, actualOriginalCertifiedSuccessorClosure p,
      actualOriginalAccessibilityIntroduction p⟩⟩

#print axioms exact_Reinstall
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallProof
