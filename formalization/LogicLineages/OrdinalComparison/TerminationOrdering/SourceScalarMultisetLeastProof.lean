module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceScalarMultisetLeastTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceScalarMultisetLeastProof
open OrdinaryArithmeticCarrier PositiveArithmeticOperators DirectMultisetAccessibleSubtype

theorem actualScalarMembersToMultiset : SourceScalarMultisetLeastTargets.ActualScalarMembersToMultiset := by
  intro n arity Gamma
  obtain ⟨scalar, multiset, hcal, hfinish⟩ :=
    SourceMultisetLeastMembershipProof.actualConditionalLeastMembership n arity Gamma
  refine ⟨scalar, multiset, hcal, ?_⟩
  intro context code ctx values hc hclosed hd hmembers
  have hfacts (x : Nat) (hx : x ∈ values) :=
    PositiveArithmeticAccessibilityProof.leastImpliesAccessibility scalar context
      (encodedScalar n arity Gamma context) (encodedR n arity Gamma context)
      (hcal context).1 x (hmembers x hx)
  have hbits : ∀ x ∈ values,
      NumberedNumericCarrier.canonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma x = true := by
    intro x hx
    obtain ⟨ctx', hc', hbit⟩ := (hfacts x hx).1
    have he : ctx = ctx' := Option.some.inj (hc.symm.trans hc')
    subst ctx'
    exact hbit
  have hcarrier : encodedList n arity Gamma context code := by
    refine ⟨ctx, values, hc, hd, ?_⟩
    exact List.all_eq_true.mpr hbits
  have hm : MembersAccessible
      (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2) values := by
    intro x hx
    apply Subrelation.accessible (r := fun successor source => encodedR n arity Gamma context source successor)
      ?_ (hfacts x hx).2
    intro successor source hrel
    exact ⟨ctx, hc, hrel⟩
  exact hfinish context code ctx values hc hclosed hd hcarrier hm

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceScalarMultisetLeastProof
