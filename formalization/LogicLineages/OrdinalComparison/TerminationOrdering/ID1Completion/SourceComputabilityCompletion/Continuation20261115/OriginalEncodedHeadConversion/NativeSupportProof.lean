module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportConstructorEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)

theorem splitStepValue (index q r : Nat) :
    evaluate splitStep (ofFn ![index,Nat.pair q r]) =
      if r = 0 then Nat.pair q 1 else Nat.pair (q+1) 0 := by
  simp only [splitStep,evalBranch,rightOfEvaluation,leftOfEvaluation,pairOfEvaluation,
    succOfEvaluation,constantEvaluation,projectionEvaluation,get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Nat.unpair_pair]

theorem splitValue (raw : Nat) :
    evaluate split (ofFn ![raw]) = Nat.pair (raw/2) (raw%2) := by
  change Nat.rec (motive := fun _ => Nat) 0
    (fun index state => evaluate splitStep (index ::ᵥ state ::ᵥ nil)) raw = _
  induction raw with
  | zero => rfl
  | succ raw ih =>
    change evaluate splitStep (raw ::ᵥ Nat.rec (motive := fun _ => Nat) 0
      (fun index state => evaluate splitStep (index ::ᵥ state ::ᵥ nil)) raw ::ᵥ nil) = _
    rw [ih]
    change evaluate splitStep (ofFn ![raw,Nat.pair (raw/2) (raw%2)]) = _
    rw [splitStepValue]
    have hm : raw % 2 < 2 := Nat.mod_lt raw (by decide)
    split_ifs with h
    · congr 1 <;> omega
    · congr 1 <;> omega

theorem halfValue (raw : Nat) : evaluate half (ofFn ![raw]) = raw/2 := by
  change evaluate InternalUnpair.left (ofFn ![evaluate split (ofFn ![raw])]) = _
  rw [splitValue,leftEvaluation]
  simp only [get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair]

theorem bitValue (raw : Nat) : evaluate bit (ofFn ![raw]) = raw%2 := by
  change evaluate InternalUnpair.right (ofFn ![evaluate split (ofFn ![raw])]) = _
  rw [splitValue,rightEvaluation]
  simp only [get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair]

theorem sumCaseValue (left right : Program 1) (raw : Nat) :
    evaluate (sumCase left right) (ofFn ![raw]) =
      if raw%2 = 0 then evaluate left (ofFn ![raw/2]) else evaluate right (ofFn ![raw/2]) := by
  rw [sumCase,evalBranch,bitValue]
  split_ifs <;> change evaluate _ (ofFn ![evaluate half (ofFn ![raw])]) = _ <;> rw [halfValue]

theorem sumLeftValue (left right : Program 1) (raw : Nat) :
    evaluate (sumCase left right) (ofFn ![2*raw]) = evaluate left (ofFn ![raw]) := by
  rw [sumCaseValue]
  have hmod : 2*raw%2=0 := by omega
  have hdiv : 2*raw/2=raw := by omega
  rw [hmod,if_pos rfl,hdiv]

theorem sumRightValue (left right : Program 1) (raw : Nat) :
    evaluate (sumCase left right) (ofFn ![2*raw+1]) = evaluate right (ofFn ![raw]) := by
  rw [sumCaseValue]
  have hmod : (2*raw+1)%2=1 := by omega
  have hdiv : (2*raw+1)/2=raw := by omega
  rw [hmod,if_neg (by decide),hdiv]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.NativeSupportProof
