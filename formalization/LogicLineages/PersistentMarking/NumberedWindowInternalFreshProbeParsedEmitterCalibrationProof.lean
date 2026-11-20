module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationStatementChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowFreeAddress (freshName)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowInternalSparsePathEnvelope (run applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (bothEvaluation branchEvaluation zeroEvaluation)
open NumberedWindowInternalFreshProbeEmitter
  (Selectors calibrated probeFields goodSpec contextSpec typeSpec nameSpec)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates arrowMissing exactCoordinates)

private theorem guardValue (scalarProg : Program 1) (q : Nat) :
    run (selectedGuard scalarProg) q =
      if run scalarProg q = 1 ∧ run addressGood q = 1 ∧ run arrowGood q = 1 then 1 else 0 := by
  unfold selectedGuard parserGuard run
  rw [GorbowVerifierNormalization.StatementChecks.actualEvaluation.2,bothEvaluation,bothEvaluation]
  by_cases hs : evaluate scalarProg (q ::ᵥ nil) = 1 <;>
    by_cases ha : evaluate addressGood (q ::ᵥ nil) = 1 <;>
    by_cases hw : evaluate arrowGood (q ::ᵥ nil) = 1 <;> simp [hs,ha,hw]

private theorem gatedValue (g datum : Program 1) (q : Nat) :
    run (gated g datum) q = if run g q = 0 then 0 else run datum q := by
  unfold gated run
  rw [branchEvaluation,zeroEvaluation]

private def agreesAt (s : Settings) (p : Selectors) (q : Nat) : Prop :=
  run p.good q = goodSpec s q ∧ run p.context q = contextSpec s q ∧
  run p.domain q = typeSpec s q ∧ run p.name q = nameSpec s q

private theorem rejectAt (s : Settings) (scalarProg bound : Program 1) (q : Nat)
    (hg : run (selectedGuard scalarProg) q = 0) (hf : probeFields s q = none) :
    agreesAt s (selected scalarProg bound) q := by
  simp [agreesAt,selected,gatedValue,hg,hf,goodSpec,contextSpec,typeSpec,nameSpec]

private theorem selectAt (s : Settings) (scalarProg bound : Program 1)
    (cal : InputCalibrated s scalarProg bound) (q : Nat) :
    agreesAt s (selected scalarProg bound) q := by
  have hsRun : run scalarProg q = (scalar s q).toNat := cal.1 q
  cases hs : scalar s q with
  | false =>
    apply rejectAt s scalarProg bound q
    · simp [guardValue,hsRun,hs]
    · simp [probeFields,hs]
  | true =>
    cases hv : addressView q with
    | none => simp [scalar,hv] at hs
    | some a =>
      rcases a with ⟨ctx,r,k⟩
      cases ha : arrowView r with
      | none =>
        obtain ⟨_,_,_,hresult,_⟩ := addressCoordinates hv
        have hno := arrowMissing hresult ha
        apply rejectAt s scalarProg bound q
        · simp [guardValue,hno]
        · simp [probeFields,hs,hv,ha]
      | some arrow =>
        rcases arrow with ⟨dom,cod⟩
        obtain ⟨_,haddr,harrow,hctx,_,hk,hdom,_⟩ := exactCoordinates q ctx r k dom cod hv ha
        have hg : run (selectedGuard scalarProg) q = 1 := by
          simp [guardValue,hsRun,hs,haddr,harrow]
        have hb : run (applyUnary bound rawLeast) q = freshName k := by
          rw [applyValue,hk]
          exact cal.2 k
        have hf : probeFields s q = some (pack ctx,dom,freshName k) := by
          simp [probeFields,hs,hv,ha]
        simp [agreesAt,selected,gatedValue,hg,hf,hctx,hdom,hb,goodSpec,contextSpec,typeSpec,nameSpec]

theorem coordinatesCalibration (s : Settings) (scalarProg bound : Program 1)
    (cal : InputCalibrated s scalarProg bound) : calibrated s (selected scalarProg bound) :=
  ⟨fun q => (selectAt s scalarProg bound cal q).1,
   fun q => (selectAt s scalarProg bound cal q).2.1,
   fun q => (selectAt s scalarProg bound cal q).2.2.1,
   fun q => (selectAt s scalarProg bound cal q).2.2.2⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterCalibrationProof
