module
public import LogicLineages.OrdinalComparison.WWSourceClassesFullTargets
public import LogicLineages.OrdinalComparison.WWSourceFinitePositiveProof
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileProof
public import LogicLineages.OrdinalComparison.WWSourcePositivePolynomialProof
public import LogicLineages.OrdinalComparison.WWSourcePolynomialIndexProof
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open ForwardTranslation

theorem actualSourceClasses : Targets.ActualSourceClasses := by
  refine ⟨actualRecursorFreePositiveFinite, ?_⟩
  intro Γ hΓ τ p t ht
  obtain ⟨v, hv, s, hs, hh⟩ := actualLevelTwoSourceHeadProfile Γ hΓ τ p t ht
  refine ⟨v, hv, s, hs, fun c hc => ?_⟩
  exact sourcePolynomialIndexLimit _ (closedPositiveValuePositive c)
    (positiveHeightOnePolynomialBound c (hh c hc))
end LogicLineages.OrdinalComparison.Source.SourceClasses
