module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalPairing (pairing)
open InternalPairingEvaluationProof (exactPairingEvaluation)
open NumberedWindowCoverBoundsAlgorithm (bounds termNext termMeasure)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverTypeLeafMeasureNumericProof (exact_CoverTypeLeafSharedMeasure)
open NumberedWindowInternalCoverNamedLeafMeasureTargets

private theorem fieldValue {raw tag ty i : Nat} (read : unpackNode raw = some (tag,[ty,i])) :
    run (field 1) raw = i := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt tag (pack [ty,i]))).2
  have middle : run cellTail (pack [ty,i]) = pack [i] := (headTailOfCell (cellAt ty (pack [i]))).2
  have inner : run cellHead (pack [i]) = i := (headTailOfCell (cellAt i (pack []))).1
  change run (field 1) (NumberedWindowPairAlgorithm.pair tag (pack [ty,i]) + 1) = i
  simp only [field,cursor,applyValue,outer,middle,inner]

private theorem ownPair {raw tag ty i : Nat} (read : unpackNode raw = some (tag,[ty,i])) :
    evaluate namedMeasurePair (raw ::ᵥ nil) = Encodable.encode ((1,i) : Nat × Nat) := by
  change evaluate (.composition pairing
    (Fin.cons (literal 1 1) (Fin.cons (field 1) Fin.elim0))) (raw ::ᵥ nil) = _
  rw [compositeTwo,literalEvaluation]
  change evaluate pairing (1 ::ᵥ run (field 1) raw ::ᵥ nil) = _
  rw [fieldValue read,exactPairingEvaluation]
  simp only [Encodable.encode_prod_val,Encodable.encode_nat]

private theorem headerBits (tag n : Nat) :
    run (header tag 2) n = 0 ∨ run (header tag 2) n = 1 := by
  simp only [run,header,nodeGood]
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem branchPaid (b : Bool) (raw : Nat)
    (leaf : run (header b.toNat 2) raw = 1) :
    evaluate namedMeasurePair (raw ::ᵥ nil) = Encodable.encode (bounds raw).1 := by
  obtain ⟨fields,parse,len⟩ := (exact_CoverHeaderUnpackNode b.toNat 2 raw).mp leaf
  rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
  have exactBounds : (bounds raw).1 = ((1,i) : Nat × Nat) := by
    cases b <;>
      simp only [bounds,termNext,parse,Option.map_some,Option.getD_some] <;>
      first
      | change termMeasure _ 0 [ty,i] = (1,i)
        rfl
      | change termMeasure _ 1 [ty,i] = (1,i)
        rfl
  rw [ownPair parse,exactBounds]

theorem exact_CoverNamedLeafMeasureBase : ExactCoverNamedLeafMeasureBase := by
  intro M calibrated n
  rw [namedMeasureBase,evalBranch]
  rcases headerBits 0 n with zero | one
  · change evaluate (header 0 2) (n ::ᵥ nil) = 0 at zero
    rw [if_pos zero,evalBranch]
    rcases headerBits 1 n with zero' | one'
    · change evaluate (header 1 2) (n ::ᵥ nil) = 0 at zero'
      rw [if_pos zero']
      exact calibrated n
    · change evaluate (header 1 2) (n ::ᵥ nil) = 1 at one'
      rw [one',if_neg (by decide)]
      exact branchPaid true n one'
  · change evaluate (header 0 2) (n ::ᵥ nil) = 1 at one
    rw [one,if_neg (by decide)]
    exact branchPaid false n one

theorem exact_CoverNamedLeafSharedMeasure : ExactCoverNamedLeafSharedMeasure := by
  intro M calibrated
  exact exact_CoverTypeLeafSharedMeasure (namedMeasureBase M) (exact_CoverNamedLeafMeasureBase M calibrated)

#print axioms exact_CoverNamedLeafMeasureBase
#print axioms exact_CoverNamedLeafSharedMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureNumericProof
