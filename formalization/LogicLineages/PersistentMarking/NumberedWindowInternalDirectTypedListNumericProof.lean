module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryScratchNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowDirectAlgorithm (typedList)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectBoundaryScratchNumericProof (exact_TypedScratchFromOriginalMap)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne predEvaluation)
open NumberedWindowInternalDirectTypedListTargets

theorem exact_NumericJRaw : ExactNumericJRaw := by
  intro i scalar fit raw
  let xs := raw ::ᵥ nil
  have parsed : evaluate parser xs = encodeResult (unpack raw) := exact_ActualEncodedOutput raw
  change evaluate (jRaw i) xs = _
  rw [jRaw,evalBranch,parsed]
  unfold typedList
  cases h : unpack raw with
  | none => rfl
  | some payload =>
    change (if numbersNumber payload + 1 = 0 then 0 else evaluate (typedPayload i) xs) =
      (payload.all scalar).toNat
    rw [if_neg (Nat.succ_ne_zero _),typedPayload,compositeOne]
    have hd : evaluate parsedPayload xs = numbersNumber payload := by
      change evaluate (.composition predOne (Fin.cons parser Fin.elim0)) xs = _
      rw [compositeOne,parsed,h]
      exact predEvaluation (numbersNumber payload + 1)
    rw [hd]
    exact exact_TypedScratchFromOriginalMap i scalar fit payload

#print axioms exact_NumericJRaw
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListNumericProof
