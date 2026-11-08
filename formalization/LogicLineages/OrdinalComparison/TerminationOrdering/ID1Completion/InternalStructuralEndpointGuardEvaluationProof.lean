module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecTotalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathPrimrecSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardEvaluationProof
open Source NumberedRewriteReduction NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative
open InternalStructuralEndpointGuard InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open NumberedQuotientPathPrimrecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

 theorem actualOriginalMembershipProgramExists :
    InternalStructuralEndpointGuardTargets.ActualOriginalMembershipProgramExists := by
  intro S
  have hd : Primrec (fun v : List.Vector Nat 1 => decodeType (v.get 0)) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
  have hm : PrimrecPred (fun p : List.Vector Nat 1 × Ty => p.2 ∈ S) :=
    (NumberedHeadWindowPrimrecProof.memberPrimitive Ty).comp Primrec.snd (Primrec.const S)
  have hp : Primrec (fun v : List.Vector Nat 1 => membershipValue S (v.get 0)) :=
    ((Primrec.dom_bool Bool.toNat).comp (optionAnyPrimitive hd hm.decide.to₂)).of_eq (by
      intro v
      cases h : decodeType (v.get 0) <;>
        simp only [membershipValue,h,Option.any_none,Option.any_some,Bool.toNat_false])
  exact Proof.allPrimitiveFunctions 1 _ hp

 theorem atEvaluation (p : Program 1) (i : Fin 5) (v : List.Vector Nat 5) :
    evaluate (.composition p (fun _ : Fin 1 => .projection i)) v =
      evaluate p (List.Vector.ofFn ![v.get i]) := rfl

 theorem typeGuardEvaluation (v : List.Vector Nat 5) :
    evaluate InternalApplicationStepPeel.endpointTypeGuard v =
      if (Nat.unpair (v.get 2)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
        (Nat.unpair (v.get 3)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
        (Nat.unpair (v.get 4)).1 = v.get 0 then 1 else 0 := by
  simp only [InternalApplicationStepPeel.endpointTypeGuard,conjunctionEvaluation,
    sameEvaluation,leftOfEvaluation,consOfEvaluation,evaluate]
  split_ifs <;> simp_all

 theorem packedTag (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (x : Nat) (q : Packed (Fin n) arity Gamma)
    (h : decodePackedNumber n arity Gamma x = some q) :
    (Nat.unpair x).1 = typeNumber q.1 := by
  rw [← NumberedNumericDecodingProof.packedNumericSound n arity Gamma x q h]
  simp only [packedNumber,Nat.unpair_pair]

 theorem actualOriginalStructuralEndpointCalibration :
    InternalStructuralEndpointGuardTargets.ActualOriginalStructuralEndpointCalibration := by
  intro n arity symbols S Gamma validity member hv hm v
  obtain ⟨sigma,hd,hdn⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 0)
  obtain ⟨tau,he,hen⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 1)
  have hs := hv.1 (List.Vector.ofFn ![v.get 2])
  have ht := hv.2 (List.Vector.ofFn ![v.get 3])
  have ha := hv.1 (List.Vector.ofFn ![v.get 4])
  have hm' := hm (List.Vector.ofFn ![v.get 1])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero] at hs ht ha hm'
  simp only [endpoint,conjunctionEvaluation,sourceAt,targetAt,argumentAt,membershipAt,
    atEvaluation,hs,ht,ha,hm',typeGuardEvaluation,InternalOriginalStepGuard.sourceValidityValue,
    InternalOriginalStepGuard.targetValidityValue,rawCarrierTest,membershipValue,he]
  cases hq : decodeUniverse n arity symbols S Gamma (v.get 2) with
  | none => simp [InternalApplicationStepPeel.endpointValue,hd,he,hq]
  | some q =>
    cases hr : decodePackedNumber n arity Gamma (v.get 3) with
    | none => simp [InternalApplicationStepPeel.endpointValue,hd,he,hq,hr]
    | some r =>
      cases hb : decodeUniverse n arity symbols S Gamma (v.get 4) with
      | none => simp [InternalApplicationStepPeel.endpointValue,hd,he,hq,hr,hb]
      | some a =>
        have hqt := packedTag n arity Gamma (v.get 2) q (Option.filter_eq_some_iff.mp hq).1
        have hrt := packedTag n arity Gamma (v.get 3) r hr
        have hat := packedTag n arity Gamma (v.get 4) a (Option.filter_eq_some_iff.mp hb).1
        have harrow : 1 + Nat.pair (v.get 0) (v.get 1) = typeNumber (.arrow sigma tau) := by
          simp only [typeNumber,hdn,hen]
        rw [hqt,hrt,hat,harrow,← hdn]
        have hi := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective
        simp only [InternalApplicationStepPeel.endpointValue,hd,he,hq,hr,hb,
          Option.isSome_some,Bool.toNat_true,hi.eq_iff]
        by_cases hqs : q.1 = .arrow sigma tau <;>
          by_cases hrs : r.1 = .arrow sigma tau <;>
          by_cases has : a.1 = sigma <;> by_cases hmem : tau ∈ S <;>
          simp [hqs,hrs,has,hmem]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardEvaluationProof
