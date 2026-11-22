module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowFieldAlgorithm (unpackNode pack packNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt measureAt offsetAt)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverLambdaProvenanceProof (exact_CoverLambdaSourceProvenance)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets

private theorem current (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem shape (i old : Nat) : evaluate lambdaShape (args i old) = 1 ↔
    ∃ ty q, unpackNode (i+1) = some (2,[ty,q]) := by
  rw [lambdaShape,unaryValue,current,exact_CoverHeaderUnpackNode 2 2]
  constructor
  · rintro ⟨xs,parsed,len⟩
    rcases xs with _ | ⟨ty,_ | ⟨q,_ | ⟨a,rest⟩⟩⟩ <;> simp at len
    exact ⟨ty,q,parsed⟩
  · rintro ⟨ty,q,parsed⟩
    exact ⟨[ty,q],parsed,rfl⟩

private theorem lambdaFields {raw ty q : Nat} (read : unpackNode raw = some (2,[ty,q])) :
    run (field 0) raw = ty ∧ run (field 1) raw = q := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 2 (pack [ty,q]))).2
  have inner : run cellHead (pack [ty,q]) = ty ∧ run cellTail (pack [ty,q]) = pack [q] :=
    headTailOfCell (cellAt ty (pack [q]))
  have final : run cellHead (pack [q]) = q := (headTailOfCell (cellAt q (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 2 (pack [ty,q]) + 1) = ty ∧ _
  simp only [field,cursor,applyValue,packNode,outer,inner.1,inner.2,final] <;> simp

private theorem selectField (j i old value : Nat)
    (found : run (field j) (i+1) = value) : evaluate (childAt j) (args i old) = value := by
  rw [childAt,unaryValue,current]
  exact found

private theorem lookupValue (i old q : Nat)
    (selected : evaluate (childAt 1) (args i old) = q) :
    evaluate (measureAt 1) (args i old) = evaluate lookup ((i-q) ::ᵥ old ::ᵥ nil) := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,selected]
  change evaluate lookup (evaluate InternalEqualityTest.subtract (q ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

theorem exact_CoverLambdaSyntaxStepCalibration : ExactCoverLambdaSyntaxStepCalibration := by
  intro V T cv ct i old previous
  change evaluate (lambdaSyntaxUpdate V T) (args i old) = (syntaxBits (i+1)).1.toNat
  rw [lambdaSyntaxUpdate,evalBranch]
  by_cases lam : ∃ ty q, unpackNode (i+1) = some (2,[ty,q])
  · obtain ⟨ty,q,read⟩ := lam
    obtain ⟨small,valid,_⟩ := exact_CoverLambdaSourceProvenance (i+1) ty q read
    have slots := lambdaFields read
    have tyAt := selectField 0 i old ty slots.1
    have qAt := selectField 1 i old q slots.2
    have earlier : evaluate (earlierAt 1) (args i old) = 1 := by
      rw [earlierAt,binaryValue,qAt,current,exactLessThanEvaluation,if_pos small]
    have guard : evaluate lambdaGuard (args i old) = 1 :=
      (conjunctionOne lambdaShape (earlierAt 1) (args i old)).mpr
        ⟨(shape i old).mpr ⟨ty,q,read⟩,earlier⟩
    have actual : (syntaxBits (i+1)).1 = (typeBit ty && (syntaxBits q).1) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [Bool.and_eq_true] using valid
    rw [guard,if_neg (by decide),lambdaAccept,actualConjunctionEvaluation,lambdaTypeSlot,
      unaryValue,tyAt,ct ty,lookupValue i old q qAt,previous q small,actual]
    cases h : typeBit ty <;> cases k : (syntaxBits q).1 <;> rfl
  · have miss : evaluate lambdaShape (args i old) ≠ 1 := fun pass => lam ((shape i old).mp pass)
    have guard : evaluate lambdaGuard (args i old) = 0 := by
      rw [lambdaGuard,actualConjunctionEvaluation]
      simp [miss]
    rw [guard,if_pos rfl,unaryValue,current]
    exact cv (i+1)

private theorem selectedRow (V T : Program 1) (cv : TermSyntaxCalibrated V) (ct : TypeSyntaxCalibrated T)
    (n : Nat) :
    evaluate (scratchRow (constantZero 2) (lambdaSyntaxUpdate V T)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      (syntaxBits n).1.toNat := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      apply exact_CoverLambdaSyntaxStepCalibration V T cv ct
      intro child small
      rw [lookupAt (constantZero 2) (lambdaSyntaxUpdate V T) (0 ::ᵥ 0 ::ᵥ nil)
        i child (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverLambdaSyntaxCalibration : ExactCoverLambdaSyntaxCalibration := by
  intro V T cv ct n
  unfold lambdaSyntax run
  rw [selectedMeasure,compositeThree]
  exact selectedRow V T cv ct n

#print axioms exact_CoverLambdaSyntaxStepCalibration
#print axioms exact_CoverLambdaSyntaxCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowNumericProof
