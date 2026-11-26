module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
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
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open InternalPairingEvaluationProof (exactPairingEvaluation)
open InternalUnpairEvaluationProof (exactUnpairEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowFieldAlgorithm (unpackNode pack packNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt measureAt offsetAt)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverLambdaProvenanceProof (exact_CoverLambdaSourceProvenance)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaShape lambdaGuard)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne callTwo)
open NumberedWindowInternalCoverLambdaMeasureRowTargets

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

private theorem oneValue {n : Nat} (p : Program 1) (q : Program n) (xs : List.Vector Nat n) :
    evaluate (callOne p q) xs = evaluate p (evaluate q xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun _ : Fin 1 => evaluate q xs)) = _
  rw [vectorOne]

private theorem twoValue {n : Nat} (p : Program 2) (q r : Program n) (xs : List.Vector Nat n) :
    evaluate (callTwo p q r) xs = evaluate p (evaluate q xs ::ᵥ evaluate r xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun i => evaluate ((![q,r] : Fin 2 → Program n) i) xs)) = _
  rw [vectorTwo] <;> rfl

theorem exact_CoverLambdaBumpCalibration : ExactCoverLambdaBumpCalibration := by
  intro d w
  let m := Encodable.encode (d,w)
  have parts : Nat.unpair m = (d,w) := by
    simp only [m,Encodable.encode_prod_val,Encodable.encode_nat,Nat.unpair_pair]
  unfold run
  rw [lambdaBump,twoValue,successorDepth,oneValue,(exactUnpairEvaluation m).1,(exactUnpairEvaluation m).2,parts]
  change evaluate InternalPairing.pairing ((d+1) ::ᵥ w ::ᵥ nil) = Encodable.encode (d+1,w)
  rw [exactPairingEvaluation] <;> simp only [Encodable.encode_prod_val,Encodable.encode_nat]

theorem exact_CoverLambdaMeasureStepCalibration : ExactCoverLambdaMeasureStepCalibration := by
  intro M cm i old previous
  change evaluate (lambdaMeasureUpdate M) (args i old) = Encodable.encode (bounds (i+1)).1
  rw [lambdaMeasureUpdate,evalBranch]
  by_cases lam : ∃ ty q, unpackNode (i+1) = some (2,[ty,q])
  · obtain ⟨ty,q,read⟩ := lam
    obtain ⟨small,_,coordinates⟩ := exact_CoverLambdaSourceProvenance (i+1) ty q read
    have qAt := selectField 1 i old q (lambdaFields read).2
    have earlier : evaluate (earlierAt 1) (args i old) = 1 := by
      rw [earlierAt,binaryValue,qAt,current,exactLessThanEvaluation,if_pos small]
    have guard : evaluate lambdaGuard (args i old) = 1 :=
      (conjunctionOne lambdaShape (earlierAt 1) (args i old)).mpr
        ⟨(shape i old).mpr ⟨ty,q,read⟩,earlier⟩
    rw [guard,if_neg (by decide),unaryValue,lookupValue i old q qAt,previous q small,coordinates]
    exact exact_CoverLambdaBumpCalibration (bounds q).1.1 (bounds q).1.2
  · have miss : evaluate lambdaShape (args i old) ≠ 1 := fun pass => lam ((shape i old).mp pass)
    have guard : evaluate lambdaGuard (args i old) = 0 := by
      rw [lambdaGuard,actualConjunctionEvaluation]
      simp [miss]
    rw [guard,if_pos rfl,unaryValue,current]
    exact cm (i+1)

private theorem selectedRow (M : Program 1) (cm : TermMeasureCalibrated M) (n : Nat) :
    evaluate (scratchRow (constantZero 2) (lambdaMeasureUpdate M)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      Encodable.encode (bounds n).1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      apply exact_CoverLambdaMeasureStepCalibration M cm
      intro child small
      rw [lookupAt (constantZero 2) (lambdaMeasureUpdate M) (0 ::ᵥ 0 ::ᵥ nil)
        i child (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverLambdaMeasureCalibration : ExactCoverLambdaMeasureCalibration := by
  intro M cm n
  unfold lambdaMeasure
  rw [selectedMeasure,compositeThree]
  exact selectedRow M cm n

#print axioms exact_CoverLambdaBumpCalibration
#print axioms exact_CoverLambdaMeasureStepCalibration
#print axioms exact_CoverLambdaMeasureCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowNumericProof
