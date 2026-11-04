module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceMultisetLeastMembershipTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceMultisetLeastMembershipProof

theorem actualConditionalLeastMembership :
    SourceMultisetLeastMembershipTargets.ActualConditionalLeastMembership := by
  intro n arity Gamma
  obtain ⟨scalar, multiset, hcal, hleast⟩ :=
    SourceArithmeticAccessibilityProof.sourceLeastAccessibility n arity Gamma
  refine ⟨scalar, multiset, hcal, ?_⟩
  intro context code ctx values hc hclosed hd hcarrier hmembers
  have hacc := SourceDirectAccessibilityProof.actualDecodedAccessibility
    n arity Gamma context code ctx values hc hd hmembers
  exact ((hleast context ⟨ctx, hc, hclosed⟩ code).2).mpr ⟨hcarrier, hacc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceMultisetLeastMembershipProof
