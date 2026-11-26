module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityJointInductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceConstructorComputabilityJointInductionProof RankedPrecedenceCertificate

theorem actualNumberedConstructorComputable :
    SourceRankedConstructorComputabilityTargets.ActualNumberedConstructorComputable := by
  intro n arity Gamma context ctx scalar hc hclosed hcal rank hrank k f tau base types extras hg hm
  have hb : ArgumentsC context ctx scalar base :=
    (argumentsC_iff base).mpr (fun p hp => hm p (List.mem_append_left _ hp))
  have he : ArgumentsC context ctx scalar extras :=
    (argumentsC_iff extras).mpr (fun p hp => hm p (List.mem_append_right _ hp))
  exact (jointByRank hc hclosed hcal rank hrank (headRank rank f) (ArgumentValues ctx base)
    (argumentsAccessible hc hclosed hcal hb)).1 k f tau base types extras rfl (List.Perm.refl _) hg hb he

theorem actualOrdinaryConstructorComputable :
    SourceRankedConstructorComputabilityTargets.ActualOrdinaryConstructorComputable := by
  intro n arity Gamma context ctx scalar hc hclosed hcal rank hrank f base hg hm
  have hb : ArgumentsC context ctx scalar base := (argumentsC_iff base).mpr hm
  exact (jointByRank hc hclosed hcal rank hrank (headRank rank f) (ArgumentValues ctx base)
    (argumentsAccessible hc hclosed hcal hb)).2 f base rfl (List.Perm.refl _) hg hb
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityProof
