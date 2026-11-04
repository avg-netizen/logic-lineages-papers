module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilitySupportProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticTypedCarrier
open NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative

theorem encodedTypedWitness (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (hc : Encodable.decode context = some ctx)
    (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2)) (tau : Ty) (value : Nat)
    (h : encodedTyped n arity Gamma context (typeNumber tau) value) :
    ∃ a : AuxTerm (Fin n) arity Gamma tau, InUniverse ctx.1.1 ctx.1.2 a ∧
      representativeCode ctx.1.1 ctx.1.2 ⟨tau,a⟩ = value := by
  obtain ⟨ctx', upsilon, hc', ht, hbit⟩ := h
  have hectx : ctx = ctx' := Option.some.inj (hc.symm.trans hc')
  subst ctx'
  have hety : tau = upsilon := Option.some.inj ((NumberedNumericDecodingProof.typeNumericRoundTrip tau).symm.trans ht)
  subst upsilon
  obtain ⟨⟨rho,a⟩, ha, he, hrep⟩ :=
    (NumberedTypedCarrierProof.typedCanonicalCarrier n arity ctx.1.1 ctx.1.2 hclosed Gamma tau value).mp hbit
  change rho = tau at he
  cases he
  exact ⟨a,ha,hrep⟩

theorem encodedTypedOfTerm (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (hc : Encodable.decode context = some ctx)
    (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2)) (tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma tau) (hq : InUniverse ctx.1.1 ctx.1.2 q) :
    encodedTyped n arity Gamma context (typeNumber tau) (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) := by
  refine ⟨ctx,tau,hc,NumberedNumericDecodingProof.typeNumericRoundTrip tau,?_⟩
  exact (NumberedTypedCarrierProof.typedCanonicalCarrier n arity ctx.1.1 ctx.1.2 hclosed Gamma tau _).mpr
    ⟨⟨tau,q⟩,hq,rfl,rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilitySupportProof
