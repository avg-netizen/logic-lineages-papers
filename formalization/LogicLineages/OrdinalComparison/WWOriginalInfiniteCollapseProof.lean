module
public import LogicLineages.OrdinalComparison.WWOriginalInfiniteCollapseTargets
public import LogicLineages.OrdinalComparison.ActualCollapse
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem actualInfiniteCollapseControlLower : Targets.ActualInfiniteCollapseControlLower := by
  intro a ha he
  have h := actualCollapse_controlledStrictness a he
    (Phi (actualOrdinalNorm a) : Ordinal)
    ((Ordinal.natCast_lt_omega0 _).trans_le ha)
    (by rw [(finiteNorm _).2])
  rwa [actualCollapse_finiteValues] at h

end LogicLineages.OrdinalComparison.Source.OriginalDomain
