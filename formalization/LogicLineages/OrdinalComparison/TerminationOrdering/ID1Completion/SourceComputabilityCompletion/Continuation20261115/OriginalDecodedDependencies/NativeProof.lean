module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedMultisetNumeric
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open InternalApplicationStepPeelEvaluationSupportProof

theorem sourceValue (v : List.Vector Nat 2) : evaluate source v = (Nat.unpair (v.get 0)).1 := by
  change evaluate InternalUnpair.left (ofFn ![v.get 0]) = _
  rw [leftEvaluation]
  rfl

theorem targetValue (v : List.Vector Nat 2) : evaluate target v = (Nat.unpair (v.get 0)).2 := by
  change evaluate InternalUnpair.right (ofFn ![v.get 0]) = _
  rw [rightEvaluation]
  rfl

theorem sourceAcceptedValue (n : Nat) (v : List.Vector Nat 2) :
    evaluate (sourceAccepted n) v = (decodeCode n (Nat.unpair (v.get 0)).1).isSome.toNat := by
  change evaluate (OriginalCodeValidityGuard.check n) (ofFn ![evaluate source v]) = _
  rw [sourceValue,OriginalCodeValidityGuard.NativeProof.nativeValidity]

theorem targetAcceptedValue (n : Nat) (v : List.Vector Nat 2) :
    evaluate (targetAccepted n) v = (decodeCode n (Nat.unpair (v.get 0)).2).isSome.toNat := by
  change evaluate (OriginalCodeValidityGuard.check n) (ofFn ![evaluate target v]) = _
  rw [targetValue,OriginalCodeValidityGuard.NativeProof.nativeValidity]

theorem nodeDecode (n node : Nat) :
    Encodable.decode (α := Continuation20261114.ExchangeNumericSuppliers.Node n) node =
    (decodeCode n (Nat.unpair node).1).bind (fun a => (decodeCode n (Nat.unpair node).2).map (fun b => (a,b))) := by
  rw [Encodable.decode_prod_val]
  rfl

theorem nodeEncode (n : Nat) (a b : Code (Fin n)) :
    Encodable.encode (a,b) = Nat.pair (codeNumber a) (codeNumber b) := by
  rw [Encodable.encode_prod_val]
  rfl

theorem crossValue (v : List.Vector Nat 2) : evaluate decodedCross v =
    evaluate NumericDependencyCross.rawDependencies (ofFn ![(Nat.unpair (v.get 0)).1,(Nat.unpair (v.get 0)).2]) := by
  change evaluate NumericDependencyCross.rawDependencies (ofFn ![evaluate source v,evaluate target v]) = _
  rw [sourceValue,targetValue]

theorem nativeOriginalSupplier : Targets.NativeOriginalSupplier := by
  intro n v
  unfold dependencies
  rw [evalBranch]
  simp only [accepted,conjunctionEvaluation,sourceAcceptedValue,targetAcceptedValue,
    constantEvaluation,Continuation20261114.ExchangeNumericSuppliers.depsValue,
    Continuation20261114.ExchangeNumericSuppliers.depsAt,nodeDecode]
  cases hs : decodeCode n (Nat.unpair (v.get 0)).1 with
  | none => simp [hs,numbersNumber]
  | some a =>
    cases ht : decodeCode n (Nat.unpair (v.get 0)).2 with
    | none => simp [hs,ht,numbersNumber]
    | some c =>
      simp only [hs,ht,Option.isSome_some,Bool.toNat_true,ite_true,Option.bind_some,Option.map_some,Option.getD_some]
      rw [crossValue]
      have ha := NumberedNumericDecodingProof.codeNumericSound n _ a hs
      have hc := NumberedNumericDecodingProof.codeNumericSound n _ c ht
      rw [← ha,← hc,NumericDependencyCross.NativeProof.dependencyValue]
      congr 1
      apply List.map_congr_left
      intro pair hp
      exact (nodeEncode n pair.1 pair.2).symm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.NativeProof
