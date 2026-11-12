module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryDeletionRows NumberedMultisetNumeric

theorem scanZero (Q : Program 2) (input parameter : Nat) :
    evaluate (scan Q) (ofFn ![0,input,parameter]) = 0 := rfl

theorem scanSuccessor (Q : Program 2) (k input parameter : Nat) :
    evaluate (scan Q) (ofFn ![k+1,input,parameter]) =
      evaluate InternalApplicationValidityStackAppend.append
        (ofFn ![evaluate (scan Q) (ofFn ![k,input,parameter]),
          evaluate InternalListCodec.consCode
            (ofFn ![evaluate (observation Q) (ofFn ![k,input,parameter]),0])]) := by
  change evaluate (step Q)
    (k ::ᵥ evaluate (scan Q) (k ::ᵥ input ::ᵥ parameter ::ᵥ nil) ::ᵥ input ::ᵥ parameter ::ᵥ nil) = _
  simp only [step,evaluate,List.Vector.get_ofFn,List.Vector.get_cons_zero,
    List.Vector.get_cons_succ,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,InternalAcceptance.constantZero]
  rfl

theorem nativeScan : OriginalHereditaryDeletionRowsTargets.NativeScan := by
  intro Q count input parameter
  induction count with
  | zero => rfl
  | succ k ih =>
    rw [scanSuccessor,ih]
    have hc : evaluate InternalListCodec.consCode
        (ofFn ![evaluate (observation Q) (ofFn ![k,input,parameter]),0]) =
        numbersNumber [evaluate (observation Q) (ofFn ![k,input,parameter])] := rfl
    rw [hc]
    have ha := OriginalContextInsertionCalibrationProof.appendNumbers
      (values Q k input parameter) [evaluate (observation Q) (ofFn ![k,input,parameter])]
    simpa only [values,List.range_succ,List.map_append,List.map_singleton] using ha

/-- The primitive row cell uses exactly the existing original all-position selectors. -/
theorem observationEvaluation (Q : Program 2) (k input parameter : Nat) :
    evaluate (observation Q) (ofFn ![k,input,parameter]) =
      evaluate Q (ofFn ![
        evaluate OriginalClassContextAllPositionObserver.erasedPacked (ofFn ![k,input,parameter]),
        evaluate OriginalClassContextAllPositionObserver.erasedParameter (ofFn ![k,input,parameter])]) := rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsNativeProof
