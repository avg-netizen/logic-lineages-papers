module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierEvaluationProof
open Source NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative NumberedTypedCarrier
open InternalOriginalTypedCarrier InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open QuotientDirectPrimrecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

 theorem actualOriginalTypedProgramExists :
    InternalOriginalTypedCarrierTargets.ActualOriginalTypedProgramExists := by
  intro n arity symbols S Gamma
  have hg (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hd := NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp (hg 1)
  have ht : Primrec (fun p : List.Vector Nat 2 × Ty =>
      typedCanonicalCarrierTest n arity symbols S Gamma p.2 (p.1.get 0)) :=
    (OrdinaryArithmeticTypedCarrierProof.typedCheckerPrimitive n arity Gamma).comp
      ((Primrec.const (symbols,S)).pair (Primrec.snd.pair ((hg 0).comp Primrec.fst)))
  have hp : Primrec (typedValue n arity symbols S Gamma) :=
    (Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd ht.to₂)
  exact Proof.allPrimitiveFunctions 2 _ hp

 theorem sourceAtEvaluation (validity : InternalOriginalStepGuard.Data) (v : List.Vector Nat 2) :
    evaluate (sourceAt validity) v =
      evaluate validity.sourceValid (List.Vector.ofFn ![v.get 0]) := rfl

 theorem sameOuterTypeEvaluation (v : List.Vector Nat 2) :
    evaluate sameOuterType v =
      if (Nat.unpair (v.get 0)).1 = v.get 1 then 1 else 0 := by
  simp only [sameOuterType,sameEvaluation,leftOfEvaluation,evaluate]

/-- This semantic implication inspects the unchanged original typed test.
It is used only for external calibration, never as an internal inference. -/
 theorem originalAcceptanceGuards (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (v : List.Vector Nat 2)
    (h : typedValue n arity symbols S Gamma v = 1) :
    InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 0) = 1 ∧
      (Nat.unpair (v.get 0)).1 = v.get 1 := by
  obtain ⟨tau,ht,htn⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 1)
  cases hq : decodeUniverse n arity symbols S Gamma (v.get 0) with
  | none =>
    simp only [typedValue,ht,Option.any_some,typedCanonicalCarrierTest,hq,
      Option.any_none,Bool.toNat_false,Nat.zero_ne_one] at h
  | some q =>
    have hb : q.1 = tau ∧ representativeCode symbols S q = v.get 0 := by
      simpa only [typedValue,ht,Option.any_some,typedCanonicalCarrierTest,hq,
        OrdinaryArithmeticQuotientProof.boolNatOne,decide_eq_true_eq] using h
    refine ⟨by simp only [InternalOriginalStepGuard.sourceValidityValue,rawCarrierTest,
      hq,Option.isSome_some,Bool.toNat_true],?_⟩
    have hpacked : decodePackedNumber n arity Gamma (v.get 0) = some q :=
      (Option.filter_eq_some_iff.mp hq).1
    rw [← NumberedNumericDecodingProof.packedNumericSound n arity Gamma (v.get 0) q hpacked]
    simp only [packedNumber,Nat.unpair_pair]
    exact (congrArg typeNumber hb.1).trans htn

 theorem actualOriginalTypedWrapperCalibration :
    InternalOriginalTypedCarrierTargets.ActualOriginalTypedWrapperCalibration := by
  intro n arity symbols S Gamma validity oldTyped hv ho v
  have hs := hv.1 (List.Vector.ofFn ![v.get 0])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero] at hs
  have hbool : typedValue n arity symbols S Gamma v = 0 ∨
      typedValue n arity symbols S Gamma v = 1 := by
    unfold typedValue
    cases (decodeType (v.get 1)).any (fun tau =>
      typedCanonicalCarrierTest n arity symbols S Gamma tau (v.get 0)) <;> simp
  rcases hbool with hz | hone
  · rw [checker,conjunctionEvaluation,conjunctionEvaluation,ho,hz]
    simp
  · obtain ⟨hsource,htag⟩ := originalAcceptanceGuards n arity symbols S Gamma v hone
    rw [checker,conjunctionEvaluation,conjunctionEvaluation,sourceAtEvaluation,
      sameOuterTypeEvaluation,hs,ho,hsource,htag,hone]
    simp

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierEvaluationProof
