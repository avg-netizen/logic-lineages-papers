module
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedChosenCombineProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure CombineCalibrated)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineNumericProof (exact_ChosenAuxMeasureCombine)
open NumberedWindowInternalAuxMeasureStepChecks (exact_PhysicalAuxMeasure)
open NumberedWindowCoverBoundsProgramProof (metrics)

/-- Select the original term-coordinate bounds independently of any
unrestricted numeric choice that hides its base measure calibration. -/
theorem exact_OriginalBaseTermMeasureChoice : ∃ baseM : Program 1, TermMeasureCalibrated baseM :=
  (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp (Primrec.fst.comp metrics))

/-- The true original measure at every raw code, with the exact literal
combine needed by the existing open parent arithmetic. This is a fresh
choice, not a replacement in an already held measure report. -/
theorem exact_OriginalMeasuredUnrestrictedChosenCombine :
    ∃ baseM : Program 1, TermMeasureCalibrated baseM ∧
      CombineCalibrated chosenCombine ∧
      TermMeasureCalibrated (selectedMeasure (measureUpdate baseM chosenCombine)) := by
  obtain ⟨baseM,baseFit⟩ := exact_OriginalBaseTermMeasureChoice
  have stepFit : CombineCalibrated chosenCombine := exact_ChosenAuxMeasureCombine
  exact ⟨baseM,baseFit,stepFit,exact_PhysicalAuxMeasure baseM chosenCombine baseFit stepFit⟩

#print axioms exact_OriginalBaseTermMeasureChoice
#print axioms exact_OriginalMeasuredUnrestrictedChosenCombine
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedChosenCombineProof
