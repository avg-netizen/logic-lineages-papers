module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaRowsNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalEqualityTestEvaluationProof (vectorOne)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
  (evalConsOf evalTernaryComposition evalLiteralLambdaFields)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (depthInstanceValue DepthInstanceFit)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit)
open NumberedWindowInternalLiteralSingletonGuardedCalibrationProof
open NumberedWindowInternalLiteralSingletonLambdaMachineProof
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowSingletonAlgorithm (output computed table)
open NumberedWindowShiftAlgorithm (earlier)

theorem exact_LiteralLambdaShapeBit (q : Nat) :
    run rawLambdaShape q = 0 ∨ run rawLambdaShape q = 1 := by
  unfold run rawLambdaShape nodeGood
  rw [actualConjunctionEvaluation]
  split <;> simp

theorem exact_LiteralLambdaShape (q : Nat) :
    run rawLambdaShape q = 1 ↔ ∃ ty b, unpackNode q = some (2,[ty,b]) := by
  rw [rawLambdaShape,nodeArity _ 2 q 2 (literalEvaluation 1 2 _)]
  constructor
  · rintro ⟨fs,report,len⟩
    rcases fs with _ | ⟨ty,_ | ⟨b,_ | ⟨last,more⟩⟩⟩ <;> simp at len
    exact ⟨ty,b,report⟩
  · rintro ⟨ty,b,h⟩
    exact ⟨[ty,b],h,rfl⟩

theorem evalPredecessor (x : Nat) :
    evaluate InternalEqualityTest.predecessor (x ::ᵥ nil) = x.pred := by
  cases x <;> rfl

/-- The written child call evaluates the fallback on the same inserted
code, the incremented depth, and the literal body field. -/
theorem exact_LiteralLambdaChildValue (U : Program 3) (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b])) :
    evaluate (lambdaChild U) (tape a d q) = evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil) := by
  have first : evaluate (.projection (0 : Fin 3)) (tape a d q) = a := rfl
  have depth : evaluate binderDepth (tape a d q) = d + 1 := by
    rw [binderDepth,evaluate,vectorOne]
    rfl
  have body : evaluate lambdaNodeBody (tape a d q) = b := by
    rw [lambdaNodeBody,atSlot]
    exact (evalLiteralLambdaFields q ty b node).2
  rw [lambdaChild,evalTernaryComposition,first,depth,body]

/-- The written emitter rebuilds the literal typed code around the
predecessor of the child value. -/
theorem exact_LiteralLambdaRebuiltValue (U : Program 3) (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b])) :
    evaluate (lambdaRebuilt U) (tape a d q) =
      packNode 2 [ty,(evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil)).pred] + 1 := by
  have typeField : run (field 0) q = ty := (evalLiteralLambdaFields q ty b node).1
  have code : evaluate (lambdaChildCode U) (tape a d q) =
      (evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil)).pred := by
    rw [lambdaChildCode,evaluate,vectorOne]
    change evaluate InternalEqualityTest.predecessor
      (evaluate (lambdaChild U) (tape a d q) ::ᵥ nil) = _
    rw [exact_LiteralLambdaChildValue U a d q ty b node,evalPredecessor]
  rw [lambdaRebuilt,evaluate,vectorOne]
  change evaluate (lambdaRebuiltCode U) (tape a d q) + 1 = _
  rw [lambdaRebuiltCode,evalConsOf,evalConsOf,evalConsOf,literalEvaluation,lambdaNodeType,atSlot,code]
  change NumberedWindowPairAlgorithm.pair 2
    (NumberedWindowPairAlgorithm.pair (run (field 0) q)
      (NumberedWindowPairAlgorithm.pair
        (evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil)).pred 0 + 1) + 1) + 1 + 1 = _
  rw [typeField]
  rfl

/-- Exact value of the written lambda instance on a literal lambda
node, for an arbitrary fallback. Zero child gives zero. -/
theorem exact_LiteralLambdaInstanceValue (U : Program 3) (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b])) :
    evaluate (lambdaInstance U) (tape a d q) =
      if evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil) = 0 then 0
      else packNode 2 [ty,(evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil)).pred] + 1 := by
  rw [lambdaInstance,evalBranch,exact_LiteralLambdaChildValue U a d q ty b node]
  by_cases failed : evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil) = 0
  · rw [if_pos failed,if_pos failed]
    rfl
  · rw [if_neg failed,if_neg failed]
    exact exact_LiteralLambdaRebuiltValue U a d q ty b node

theorem exact_LiteralLambdaDispatchValue (U : Program 3) (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b])) :
    evaluate (singletonLambdaDispatch U) (tape a d q) =
      if evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil) = 0 then 0
      else packNode 2 [ty,(evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil)).pred] + 1 := by
  have yes : run rawLambdaShape q = 1 := (exact_LiteralLambdaShape q).mpr ⟨ty,b,node⟩
  rw [singletonLambdaDispatch,evalBranch,atSlot]
  change (if run rawLambdaShape q = 0 then evaluate U (tape a d q)
    else evaluate (lambdaInstance U) (tape a d q)) = _
  rw [yes,if_neg (by decide : (1 : Nat) ≠ 0)]
  exact exact_LiteralLambdaInstanceValue U a d q ty b node

/-- Off the lambda shape the written dispatch is the fallback itself. -/
theorem exact_LiteralLambdaDispatchOther (U : Program 3) (a d q : Nat)
    (no : run rawLambdaShape q = 0) :
    evaluate (singletonLambdaDispatch U) (tape a d q) = evaluate U (tape a d q) := by
  rw [singletonLambdaDispatch,evalBranch,atSlot]
  change (if run rawLambdaShape q = 0 then evaluate U (tape a d q)
    else evaluate (lambdaInstance U) (tape a d q)) = _
  rw [no,if_pos rfl]

/-- The original singleton algorithm on a lambda node: the same type
field, and the table entry of the body at offset one. The table is the
node's own; nothing is said about how that entry was computed. -/
theorem exact_OriginalSingletonLambdaRow (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b])) :
    (computed a d q q 0).1 = packNode 2 [ty,(earlier (table a d q q) b 1).1] := by
  change ((unpackNode q).map (fun p =>
    NumberedWindowSingletonAlgorithm.termParts (table a d q q) a d 0 p.1 p.2)).getD 0 = _
  rw [node]
  rfl

theorem exact_OriginalSingletonLambdaValue (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b]))
    (well : (syntaxBits a).1 = true) (qWell : (syntaxBits q).1 = true) :
    depthInstanceValue a d q = packNode 2 [ty,(earlier (table a d q q) b 1).1] + 1 := by
  have first : (output a d q).1 =
      if ((syntaxBits a).1 && (syntaxBits q).1) = true then some (computed a d q q 0).1
      else none := rfl
  rw [depthInstanceValue,first,well,qWell,exact_OriginalSingletonLambdaRow a d q ty b node]
  rfl

/-- Finite numeric lambda row. On one guarded lambda node, the written
dispatch equals the original singleton value as soon as the fallback's
value at the incremented depth is the successor of the node's own
offset-one table entry for the body. That equation is the hypothesis
`child`; it is not derived here. -/
theorem exact_LiteralLambdaDispatchCalibratedRow (U : Program 3) (a d q ty b : Nat)
    (node : unpackNode q = some (2,[ty,b]))
    (well : (syntaxBits a).1 = true) (qWell : (syntaxBits q).1 = true)
    (child : evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil) = (earlier (table a d q q) b 1).1 + 1) :
    evaluate (singletonLambdaDispatch U) (tape a d q) = depthInstanceValue a d q := by
  rw [exact_LiteralLambdaDispatchValue U a d q ty b node,child,if_neg (Nat.succ_ne_zero _),
    Nat.pred_succ,exact_OriginalSingletonLambdaValue a d q ty b node well qWell]

/-- The exact recursion premise for the lambda row, uniformly in the
node: behind the guard, the fallback at depth `d+1` on the body returns
the successor of the parent table's offset-one entry. -/
def LambdaChildFit (U : Program 3) : Prop :=
  ∀ a d q ty b, unpackNode q = some (2,[ty,b]) →
    (syntaxBits a).1 = true → (syntaxBits q).1 = true →
    evaluate U (a ::ᵥ (d+1) ::ᵥ b ::ᵥ nil) = (earlier (table a d q q) b 1).1 + 1

/-- Guarded fit of the written dispatch. The non-lambda case is the
fallback's own guarded fit on the same tape; the lambda case is the
calibrated row with the child premise. -/
theorem exact_LiteralLambdaDispatchGuardedFit (U : Program 3)
    (uFit : GuardedDepthInstanceFit U) (childFit : LambdaChildFit U) :
    GuardedDepthInstanceFit (singletonLambdaDispatch U) := by
  intro a d q well qWell
  change evaluate (singletonLambdaDispatch U) (tape a d q) = _
  rcases exact_LiteralLambdaShapeBit q with no | yes
  · rw [exact_LiteralLambdaDispatchOther U a d q no]
    exact uFit a d q well qWell
  · obtain ⟨ty,b,node⟩ := (exact_LiteralLambdaShape q).mp yes
    exact exact_LiteralLambdaDispatchCalibratedRow U a d q ty b node well qWell
      (childFit a d q ty b node well qWell)

/-- All-input calibration of the installed lambda program, conditional
on the child premise. It reuses the saved guarded calibration. -/
theorem exact_LiteralSingletonLambdaCalibration (V : Program 1) (H : Program 2) (U : Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H)
    (uFit : GuardedDepthInstanceFit U) (childFit : LambdaChildFit U) :
    DepthInstanceFit (singletonLambda V H U) :=
  exact_LiteralSingletonLambdaCalibrationOfGuarded V H U vFit hFit
    (exact_LiteralLambdaDispatchGuardedFit U uFit childFit)

#print axioms exact_LiteralLambdaShapeBit
#print axioms exact_LiteralLambdaShape
#print axioms evalPredecessor
#print axioms exact_LiteralLambdaChildValue
#print axioms exact_LiteralLambdaRebuiltValue
#print axioms exact_LiteralLambdaInstanceValue
#print axioms exact_LiteralLambdaDispatchValue
#print axioms exact_LiteralLambdaDispatchOther
#print axioms exact_OriginalSingletonLambdaRow
#print axioms exact_OriginalSingletonLambdaValue
#print axioms exact_LiteralLambdaDispatchCalibratedRow
#print axioms LambdaChildFit
#print axioms exact_LiteralLambdaDispatchGuardedFit
#print axioms exact_LiteralSingletonLambdaCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaRowsNumericProof
