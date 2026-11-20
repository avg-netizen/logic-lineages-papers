module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterValueProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterSelectorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeEmitter NumberedWindowInternalFreshProbeEmitterNumericTargets
open NumberedWindowInternalFreshProbeEmitterValueProof
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne branchEvaluation zeroEvaluation)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowTypedProbe (probe)

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

theorem exact_PackedFreeEmitterValue : ExactPackedFreeEmitterValue := exactPackedFree

theorem exact_OriginalSelectedFreshEmitter : ExactOriginalSelectedFreshEmitter := by
  intro s
  obtain ⟨p,hp⟩ := NumberedWindowInternalFreshProbeEmitterSelectorProof.selected s
  refine ⟨p,hp,fun q => ?_⟩
  rcases hp with ⟨hg,hc,ht,hn⟩
  rw [probeFromFields,chooseFresh,branchEvaluation,hg]
  cases ho : probeFields s q with
  | none => simp [goodSpec,ho,zeroEvaluation]
  | some row =>
    have hg1 : goodSpec s q = 1 := by simp [goodSpec,ho]
    rw [hg1,if_neg (by decide : (1 : Nat) ≠ 0),compositeOne,emitSelectedValue,hc,ht,hn]
    change (packedFree (contextSpec s q) (typeSpec s q) (nameSpec s q)).succ = _
    simp [contextSpec,typeSpec,nameSpec,ho]

#print axioms exact_PackedFreeEmitterValue
#print axioms exact_OriginalSelectedFreshEmitter
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericChecks
