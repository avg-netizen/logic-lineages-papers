module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalListCodecEvaluationProof

theorem singletonValue (value : Nat) :
    evaluate InternalListCodec.consCode (ofFn ![value,0]) = numbersNumber [value] := by
  rw [InternalEqualityTestEvaluationProof.vectorTwo,consEvaluation]
  rfl

theorem zerosValue (count : Nat) :
    evaluate zeros (count ::ᵥ nil) = numbersNumber (List.replicate count 0) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change evaluate InternalListCodec.consCode
      (ofFn ![0,evaluate zeros (count ::ᵥ nil)]) = _
    rw [ih,InternalEqualityTestEvaluationProof.vectorTwo,consEvaluation]
    rfl

theorem seedValue (bound : Nat) :
    evaluate seed (bound ::ᵥ nil) = numbersNumber (List.replicate (bound+1) 0) := by
  change evaluate zeros ((bound+1) ::ᵥ nil) = _
  exact zerosValue (bound+1)

theorem rowZero (n previous : Nat) :
    evaluate (nextRow n) (ofFn ![0,previous]) =
      numbersNumber [evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,0])] := by
  change evaluate InternalListCodec.consCode (ofFn ![
    evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,0]),0]) = _
  exact singletonValue _

theorem rowSuccessor (n bound previous : Nat) :
    evaluate (nextRow n) (ofFn ![bound+1,previous]) =
      evaluate InternalApplicationValidityStackAppend.append (ofFn ![
        evaluate (nextRow n) (ofFn ![bound,previous]),
        numbersNumber [evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,bound+1])]]) := by
  change evaluate InternalApplicationValidityStackAppend.append (ofFn ![
    evaluate (nextRow n) (ofFn ![bound,previous]),
    evaluate InternalListCodec.consCode (ofFn ![
      evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,bound+1]),0])]) = _
  rw [singletonValue]

theorem rowEvaluation (n bound previous : Nat) :
    evaluate (nextRow n) (ofFn ![bound,previous]) =
      numbersNumber ((List.range (bound+1)).map (fun index =>
        evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,index]))) := by
  induction bound with
  | zero => exact rowZero n previous
  | succ bound ih =>
    rw [rowSuccessor,ih]
    have ha := OriginalContextInsertionCalibrationProof.appendNumbers
      ((List.range (bound+1)).map (fun index =>
        evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,index])))
      [evaluate (OriginalCodeDecoderStep.step n) (ofFn ![previous,bound+1])]
    simpa only [List.range_succ,List.map_append,List.map_singleton,
      InternalEqualityTestEvaluationProof.vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one] using ha

theorem nativeRows : Targets.NativeRows := by
  intro n bound previous
  rw [rowEvaluation]
  simp only [OriginalCodeDecoderStep.NativeProof.nativeCodeNext]

theorem boolRoundTrip (xs : List Bool) :
    (xs.map Bool.toNat).map (fun value => value == 1) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp only [List.map_cons,ih] <;> rfl

theorem nativeTable : Targets.NativeTable := by
  intro n bound fuel
  induction fuel with
  | zero =>
    change evaluate seed (bound ::ᵥ nil) = _
    rw [seedValue]
    simp only [NumberedCodeParserTable.codeTable,List.map_replicate]
    rfl
  | succ fuel ih =>
    change evaluate (nextRow n) (ofFn ![bound,
      evaluate (tableProgram n) (ofFn ![fuel,bound])]) = _
    rw [ih,nativeRows,numbersRoundTrip]
    simp only [Option.getD_some,boolRoundTrip,NumberedCodeParserTable.codeTable,List.map_map]
    rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.NativeProof
