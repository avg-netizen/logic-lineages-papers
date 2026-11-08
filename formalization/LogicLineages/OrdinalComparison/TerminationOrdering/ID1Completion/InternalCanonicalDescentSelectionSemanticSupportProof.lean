module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionSemanticSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative NumberedTypedCarrier
open InternalOriginalStepGuard InternalQuotientEdgeChecker

/-- Original least-class semantics, with no strengthened selection interface. -/
theorem representativeFacts (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S)) (x : Nat)
    (hx : sourceValidityValue n arity symbols S Gamma x = 1) :
    let r := targetRepresentativeValue n arity symbols S Gamma x
    r ≤ x ∧ sourceValidityValue n arity symbols S Gamma r = 1 ∧
      (Nat.unpair r).1 = (Nat.unpair x).1 ∧
      targetRepresentativeValue n arity symbols S Gamma r = r := by
  cases hd : decodeUniverse n arity symbols S Gamma x with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hx
  | some q =>
    obtain ⟨hn,hq⟩ := (NumberedNumericCarrierProof.numericUniverseDecode
      n arity symbols S Gamma x q).mp hd
    have hp := (Option.filter_eq_some_iff.mp hd).1
    have hr : targetRepresentativeValue n arity symbols S Gamma x =
        representativeCode symbols S q := by simp [targetRepresentativeValue,hp]
    rw [hr]
    rcases q with ⟨tau,q⟩
    obtain ⟨r,hu,hd',he⟩ := NumberedNumericApplicationSupportProof.decodedRepresentative
      n arity symbols S hc Gamma tau q hq
    refine ⟨?_,?_,?_,?_⟩
    · rw [← hn]
      exact NumberedLeastCodeRepresentativeProof.representativeMinimal
        n arity symbols S hc Gamma ⟨tau,q⟩ ⟨tau,q⟩ hq (.refl _)
    · simp [sourceValidityValue,rawCarrierTest,hd']
    · rw [← hn]
      simpa only [packedNumber,Nat.unpair_pair] using
        InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeOuterType
          n arity symbols S Gamma ⟨tau,q⟩
    · simp only [targetRepresentativeValue,(Option.filter_eq_some_iff.mp hd').1]
      exact he

/-- The exact original carrier is validity, raw tag, and original R-fixedness. -/
theorem typedCharacterization (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (v : List.Vector Nat 2) :
    InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v =
      if sourceValidityValue n arity symbols S Gamma (v.get 0) = 1 ∧
          (Nat.unpair (v.get 0)).1 = v.get 1 ∧
          targetRepresentativeValue n arity symbols S Gamma (v.get 0) = v.get 0
      then 1 else 0 := by
  obtain ⟨tau,ht,htn⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 1)
  cases hd : decodeUniverse n arity symbols S Gamma (v.get 0) with
  | none => simp only [InternalOriginalTypedCarrier.typedValue,ht,Option.any_some,
      typedCanonicalCarrierTest,sourceValidityValue,rawCarrierTest,hd,Option.any_none,
      Option.isSome_none,Bool.toNat_false,Nat.zero_ne_one,false_and,ite_false]
  | some q =>
    have hp := (Option.filter_eq_some_iff.mp hd).1
    have hn := NumberedNumericDecodingProof.packedNumericSound n arity Gamma (v.get 0) q hp
    have htag : (Nat.unpair (v.get 0)).1 = v.get 1 ↔ q.1 = tau := by
      rw [← hn]
      simp only [packedNumber,Nat.unpair_pair,← htn,
        NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective.eq_iff]
    simp only [InternalOriginalTypedCarrier.typedValue,ht,Option.any_some,
      typedCanonicalCarrierTest,hd,sourceValidityValue,rawCarrierTest,
      Option.isSome_some,Bool.toNat_true,targetRepresentativeValue,hp,htag,
      true_and]
    split_ifs with h <;>
      simp only [h,true_and,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionSemanticSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionSemanticSupportProof
