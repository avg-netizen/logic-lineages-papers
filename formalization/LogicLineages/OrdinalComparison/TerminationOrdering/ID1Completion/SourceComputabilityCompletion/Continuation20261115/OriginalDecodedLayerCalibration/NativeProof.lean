module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Continuation20261114
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof
open OriginalDecodedDependencies.NativeProof
open NumberedNumericDecoding

theorem nodeValue (n : Nat) (v : List.Vector Nat 3) :
    evaluate (nodeAccepted n) v = (Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0)).isSome.toNat := by
  change evaluate (OriginalDecodedDependencies.accepted n) (ofFn ![v.get 0,v.get 2]) = _
  simp only [OriginalDecodedDependencies.accepted,conjunctionEvaluation,sourceAcceptedValue,targetAcceptedValue,nodeDecode]
  change (if (decodeCode n (Nat.unpair (v.get 0)).1).isSome.toNat = 1 ∧
    (decodeCode n (Nat.unpair (v.get 0)).2).isSome.toNat = 1 then 1 else 0) = _
  cases decodeCode n (Nat.unpair (v.get 0)).1 <;> cases decodeCode n (Nat.unpair (v.get 0)).2 <;> rfl

theorem windowValue (n : Nat) (v : List.Vector Nat 3) :
    evaluate (windowAccepted n) v = (Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2)).isSome.toNat := by
  change evaluate (OriginalDecodedWindowValidity.window n) (ofFn ![v.get 2]) = _
  rw [OriginalDecodedWindowValidity.NativeProof.nativeWindow]

theorem nativeGuard : Targets.NativeGuard := by
  intro n v
  simp only [guard,conjunctionEvaluation,nodeValue,windowValue,TransparentExchangeLayer.validValue]
  cases Encodable.decode (α := ExchangeNumericSuppliers.Node n) (v.get 0) <;>
    cases Encodable.decode (α := ExchangeNumericSuppliers.Window n) (v.get 2) <;> rfl

theorem liveFields (n : Nat) (arity : Fin n → Nat) (i : Fin 19) (hi : i ≠ 14) (hj : i ≠ 15)
    (v : List.Vector Nat 3) :
    evaluate (HeadMoveFields.fields n arity (fun _ => .composition .zero (fun j => Fin.elim0 j)) (guard n) i) v =
      TransparentExchangeLayer.fieldValue n arity i v := by
  have ht := TransparentTagFields.NativeProof.nativeTags n arity (guard n) (nativeGuard n) v
  have hm0 := EncodedMetadataFields.NativeProof.nativeMetadata n arity (guard n) (nativeGuard n) false v
  have hm1 := EncodedMetadataFields.NativeProof.nativeMetadata n arity (guard n) (nativeGuard n) true v
  have hc0 := TransparentChildFields.NativeProof.nativeChildren n arity (guard n) (nativeGuard n) false v
  have hc1 := TransparentChildFields.NativeProof.nativeChildren n arity (guard n) (nativeGuard n) true v
  fin_cases i
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using ht.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm0.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm0.2.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm0.2.2.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm0.2.2.2
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hc0.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hc0.2
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using ht.2
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm1.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm1.2.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm1.2.2.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hm1.2.2.2
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hc1.1
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using hc1.2
  · exact False.elim (hi rfl)
  · exact False.elim (hj rfl)
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using HeadMoveFields.NativeProof.nativeField n arity (guard n) (nativeGuard n) v
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using HeadResultFields.NativeProof.nativeResults n arity (guard n) (nativeGuard n) false v
  · simpa [HeadMoveFields.fields,ResultStructuralFields.fields,StructuralExchangeFields.fields,HeadMoveFields.suppliers] using HeadResultFields.NativeProof.nativeResults n arity (guard n) (nativeGuard n) true v

theorem nativeLayer : Targets.NativeLayer := by
  intro n arity v
  exact TransparentExchangeLayer.NativeProof.nativeOptional n arity
    (HeadMoveFields.fields n arity (fun _ => .composition .zero (fun j => Fin.elim0 j)) (guard n))
    (guard n) (liveFields n arity) (nativeGuard n) v
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.NativeProof
