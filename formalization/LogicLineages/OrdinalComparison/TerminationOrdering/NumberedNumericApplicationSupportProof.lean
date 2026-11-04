module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedNumericCarrier
open NumberedLeastCodeRepresentative NumberedQuotientApplication NumberedNumericApplication

theorem evaluateOnDecoded (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (sigma tau : Ty) (x y : Nat) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : decodeUniverse n arity symbols S Gamma x=some ⟨.arrow sigma tau,f⟩)
    (ha : decodeUniverse n arity symbols S Gamma y=some ⟨sigma,a⟩)
    (hfx : representativeCode symbols S ⟨.arrow sigma tau,f⟩=x)
    (hay : representativeCode symbols S ⟨sigma,a⟩=y) :
    canonicalApplication n arity symbols S Gamma sigma tau x y =
      some (representativeCode symbols S (applicationPacked f a)) := by
  simp [canonicalApplication,hf,ha,hfx,hay]

theorem decodedRepresentative (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (hc : SubtypeClosed (fun t => t∈S)) (Gamma : List Ty) (tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma tau) (hq : InUniverse symbols S q) :
    ∃ r : AuxTerm (Fin n) arity Gamma tau, InUniverse symbols S r ∧
      decodeUniverse n arity symbols S Gamma (representativeCode symbols S ⟨tau,q⟩)=some ⟨tau,r⟩ ∧
      representativeCode symbols S ⟨tau,r⟩=representativeCode symbols S ⟨tau,q⟩ := by
  obtain ⟨⟨rt,r⟩,hqr,ht,hr,hnum⟩ := NumberedTypedCarrierProof.typedRepresentativeAttained n arity symbols S hc Gamma ⟨tau,q⟩ hq
  change rt=tau at ht
  subst rt
  refine ⟨r,hr,?_,?_⟩
  · exact (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma _ ⟨tau,r⟩).mpr ⟨hnum.symm,hr⟩
  · exact ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma ⟨tau,q⟩ ⟨tau,r⟩ hq hr).mpr hqr).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationSupportProof
