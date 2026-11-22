module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericRowProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero conjunction)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThan (constantOne)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (nodeGood run field)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne conjunctionBit)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck childAt earlierAt measureAt offsetAt)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate auxAccept typeAt)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentLeaf)
open NumberedWindowInternalCoverAuxFragmentNumericTargets

private theorem current (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem shape (i old : Nat) : evaluate shapeCheck (args i old) = 1 ↔ HasAuxPayload (i+1) := by
  rw [shapeCheck,unaryValue,current]
  exact termOne (i+1)

private theorem selectField (j i old value : Nat)
    (found : run (field j) (i+1) = value) : evaluate (childAt j) (args i old) = value := by
  rw [childAt,unaryValue,current]
  exact found

private theorem lookupValue (slot i old q : Nat)
    (selected : evaluate (childAt slot) (args i old) = q) :
    evaluate (measureAt slot) (args i old) = sourceLookup i old q := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,selected]
  change evaluate InternalRawListRecursion.lookup
    (evaluate InternalEqualityTest.subtract (q ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

private theorem earlier (slot i old v : Nat) (selected : evaluate (childAt slot) (args i old) = v)
    (small : v < i+1) : evaluate (earlierAt slot) (args i old) = 1 := by
  rw [earlierAt,binaryValue,selected,current,exactLessThanEvaluation,if_pos small]

private theorem lambdaHeader (raw : Nat) : run (header 2 2) raw = 1 ↔ HasLambdaPayload raw := by
  rw [exact_CoverHeaderUnpackNode]
  constructor
  · rintro ⟨fields,h,len⟩
    rcases fields with _ | ⟨dom,_ | ⟨q,_ | ⟨third,rest⟩⟩⟩ <;> simp at len
    exact ⟨dom,q,h⟩
  · rintro ⟨dom,q,h⟩
    exact ⟨[dom,q],h,rfl⟩

private theorem oneValue (raw : Nat) : run (constantOne 1) raw = 1 := by
  simp [run,constantOne,constantZero,evaluate]

private theorem leafResult (raw : Nat) :
    (run fragmentLeaf raw = 1 ↔ ¬ HasLambdaPayload raw) ∧
    (run fragmentLeaf raw = 0 ∨ run fragmentLeaf raw = 1) := by
  let xs := raw ::ᵥ nil
  have one : evaluate (constantOne 1) xs = 1 := oneValue raw
  have zero : evaluate (constantZero 1) xs = 0 := rfl
  have headerBit : run (header 2 2) raw = 0 ∨ run (header 2 2) raw = 1 := by
    unfold header nodeGood run
    exact conjunctionBit _ _ xs
  have evaluated : run fragmentLeaf raw = if run (header 2 2) raw = 0 then 1 else 0 := by
    change evaluate (branch (header 2 2) (constantOne 1) (constantZero 1)) xs = _
    rw [evalBranch,one,zero] <;> rfl
  rcases headerBit with h | h
  · have no : ¬ HasLambdaPayload raw := by
      intro t
      rw [(lambdaHeader raw).mpr t] at h
      omega
    rw [evaluated,h,if_pos rfl]
    simp [no]
  · rw [evaluated,h,if_neg one_ne_zero]
    simp [(lambdaHeader raw).mp h]

private theorem strictGuard (i old dom cod fn arg : Nat)
    (read : unpackNode (i+1) = some (6,[dom,cod,fn,arg])) :
    evaluate certain (args i old) = 1 := by
  have fs := termFields read
  have f := selectField 2 i old fn fs.2.2.1
  have a := selectField 3 i old arg fs.2.2.2
  have fnSmall := (nodeBounds read).2 fn (by simp)
  have argSmall := (nodeBounds read).2 arg (by simp)
  simp only [certain,conjunctionOne]
  exact ⟨(shape i old).mpr ⟨dom,cod,fn,arg,read⟩,
    earlier 2 i old fn f fnSmall,earlier 3 i old arg a argSmall⟩

private theorem nonauxGuard (i old : Nat) (miss : ¬ HasAuxPayload (i+1)) :
    evaluate certain (args i old) = 0 := by
  have no : evaluate shapeCheck (args i old) ≠ 1 := fun yes => miss ((shape i old).mp yes)
  rw [certain,actualConjunctionEvaluation]
  simp [no]

theorem exact_CoverAuxFragmentNumericRow : ExactCoverAuxFragmentNumericRow := by
  intro i old
  classical
  have oneAt (slot : Nat) : evaluate (typeAt (constantOne 1) slot) (args i old) = 1 := by
    rw [typeAt,unaryValue]
    exact oneValue _
  have auxResult (dom cod fn arg : Nat) (read : unpackNode (i+1) = some (6,[dom,cod,fn,arg])) :
      fragmentRow i old = evaluate (auxAccept (constantOne 1)) (args i old) := by
    unfold fragmentRow auxSyntaxUpdate
    rw [evalBranch,strictGuard i old dom cod fn arg read,if_neg one_ne_zero]
  have leafResultAt (miss : ¬ HasAuxPayload (i+1)) :
      fragmentRow i old = run fragmentLeaf (i+1) := by
    unfold fragmentRow auxSyntaxUpdate
    rw [evalBranch,nonauxGuard i old miss,if_pos rfl,unaryValue,current] <;> rfl
  refine ⟨?_,?_,?_⟩
  · intro dom cod fn arg read
    have fields := termFields read
    have f := selectField 2 i old fn fields.2.2.1
    have a := selectField 3 i old arg fields.2.2.2
    rw [auxResult dom cod fn arg read]
    simp only [auxAccept,conjunctionOne,oneAt,lookupValue 2 i old fn f,lookupValue 3 i old arg a,true_and]
  · intro miss
    rw [leafResultAt miss]
    exact (leafResult (i+1)).1
  · by_cases has : HasAuxPayload (i+1)
    · obtain ⟨dom,cod,fn,arg,read⟩ := has
      rw [auxResult dom cod fn arg read]
      unfold auxAccept
      exact conjunctionBit _ _ _
    · rw [leafResultAt has]
      exact (leafResult (i+1)).2

#print axioms exact_CoverAuxFragmentNumericRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericRowProof
