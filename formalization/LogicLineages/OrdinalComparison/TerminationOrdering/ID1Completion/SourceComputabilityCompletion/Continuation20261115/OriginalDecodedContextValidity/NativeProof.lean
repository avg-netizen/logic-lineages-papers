module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.EnumerationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open TwoSol20261113.CalibratedPrimary.Membership
open InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem nativeTable : Targets.NativeTable := by
  intro n v
  change evaluate contains (ofFn ![evaluate (OriginalRawSyntaxTransport.constant 1 (tableListCode n)) v,v.get 0]) = _
  rw [constantEvaluation,TwoSol20261113.CalibratedPrimary.MembershipNativeProof.actualContainsNative]
  simp only [tableListCode,NumberedMultisetNumericSupportProof.numbersRoundTrip,Option.getD_some]
  exact congrArg Bool.toNat (EnumerationProof.tableDecode n (v.get 0)).symm

theorem windowLeft (n : Nat) (v : List.Vector Nat 1) :
    evaluate (.composition (OriginalDecodedWindowValidity.window n) (fun _ : Fin 1 => InternalUnpair.left)) v =
      (Encodable.decode (α := Continuation20261114.ExchangeNumericSuppliers.Window n) (Nat.unpair (v.get 0)).1).isSome.toNat := by
  change evaluate (OriginalDecodedWindowValidity.window n) (ofFn ![evaluate InternalUnpair.left v]) = _
  rw [OriginalDecodedWindowValidity.NativeProof.nativeWindow]
  change (Encodable.decode (α := Continuation20261114.ExchangeNumericSuppliers.Window n) (evaluate InternalUnpair.left v)).isSome.toNat = _
  rw [InternalApplicationCertificateConstructorsEvaluationProof.leftEvaluation]

theorem tableRight (n : Nat) (v : List.Vector Nat 1) :
    evaluate (.composition (tableGuard n) (fun _ : Fin 1 => InternalUnpair.right)) v =
      (Encodable.decode (α := Fin n → Fin n → Bool) (Nat.unpair (v.get 0)).2).isSome.toNat := by
  change evaluate (tableGuard n) (ofFn ![evaluate InternalUnpair.right v]) = _
  rw [nativeTable]
  change (Encodable.decode (α := Fin n → Fin n → Bool) (evaluate InternalUnpair.right v)).isSome.toNat = _
  rw [InternalApplicationCertificateConstructorsEvaluationProof.rightEvaluation]

theorem nativeContext : Targets.NativeContext := by
  intro n v
  rw [contextGuard,conjunctionEvaluation,windowLeft,tableRight,Encodable.decode_prod_val]
  cases Encodable.decode (α := Continuation20261114.ExchangeNumericSuppliers.Window n) (Nat.unpair (v.get 0)).1 <;>
    cases Encodable.decode (α := Fin n → Fin n → Bool) (Nat.unpair (v.get 0)).2 <;> rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.NativeProof
