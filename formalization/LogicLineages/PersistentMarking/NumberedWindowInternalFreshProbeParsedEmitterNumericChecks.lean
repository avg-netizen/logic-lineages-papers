module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterValueProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramChecks
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowTypedProbe (probe)
open NumberedWindowInternalFreshProbeEmitter
open NumberedWindowInternalFreshProbeEmitterValueProof (emitSelectedValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (branchEvaluation compositeOne zeroEvaluation)
open NumberedWindowInternalFreshProbeParsedEmitter (selected InputCalibrated)
open NumberedWindowInternalFreshProbeParsedEmitterNumericTargets
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (exactCoordinates)
open NumberedWindowInternalFreshProbeParsedEmitterCalibrationProof (coordinatesCalibration)

private theorem probeFromFields (s : Settings) (q : Nat) :
    probe s q = (probeFields s q).map (fun b => packedFree b.1 b.2.1 b.2.2) := by
  cases hs : scalar s q with
  | false => simp [probe,probeFields,hs]
  | true =>
    cases ha : addressView q with
    | none => simp [probe,probeFields,hs,ha]
    | some a =>
      cases hd : arrowView a.2.1 with
      | none => simp [probe,probeFields,hs,ha,hd]
      | some b =>
        rcases b with ⟨dom,cod⟩
        simp [probe,probeFields,hs,ha,hd,packedFree,NumberedWindowFreeAddress.freeAddress]

private theorem chosenOutput (s : Settings) (p : Selectors) (hp : calibrated s p) (q : Nat) :
    evaluate (chooseFresh p) (q ::ᵥ nil) = Encodable.encode (probe s q) := by
  obtain ⟨hg,hc,ht,hn⟩ := hp
  rw [probeFromFields,chooseFresh,branchEvaluation,hg]
  cases ho : probeFields s q with
  | none => simp [goodSpec,ho,zeroEvaluation]
  | some row =>
    have hg1 : goodSpec s q = 1 := by simp [goodSpec,ho]
    rw [hg1,if_neg (by decide : (1 : Nat) ≠ 0),compositeOne,emitSelectedValue,hc,ht,hn]
    change (packedFree (contextSpec s q) (typeSpec s q) (nameSpec s q)).succ = _
    simp [contextSpec,typeSpec,nameSpec,ho]

theorem exact_OriginalAddressArrowCoordinates : ExactOriginalAddressArrowCoordinates :=
  exactCoordinates

theorem exact_ParsedFreshCalibration : ExactParsedFreshCalibration := by
  intro s scalarProg bound cal
  have h := coordinatesCalibration s scalarProg bound cal
  exact ⟨h,chosenOutput s (selected scalarProg bound) h⟩

theorem exact_OriginalParsedFreshSelection : ExactOriginalParsedFreshSelection := by
  intro s
  obtain ⟨scalarProg,hs⟩ := NumberedWindowScalarProgramProof.scalarProgram s
  obtain ⟨bound,hb⟩ := NumberedWindowFreeAddressProgramChecks.exact_FreeAddressPrograms.2
  have h : InputCalibrated s scalarProg bound := by
    refine ⟨fun q => (hs q).trans ?_,hb⟩
    cases scalar s q <;> rfl
  exact ⟨scalarProg,bound,h,exact_ParsedFreshCalibration s scalarProg bound h⟩

#print axioms exact_OriginalAddressArrowCoordinates
#print axioms exact_ParsedFreshCalibration
#print axioms exact_OriginalParsedFreshSelection
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterNumericChecks
