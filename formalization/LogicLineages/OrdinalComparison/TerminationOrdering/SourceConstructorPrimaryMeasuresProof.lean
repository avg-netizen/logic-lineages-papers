module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowEquivalence NumberedLeastCodeRepresentative RankedPrecedenceCertificate
open SourceZeroNumberedComputability SourceZeroNumberedShapeProof SourceConstructorPrimaryMeasuresSupportProof

theorem actualPrimaryOrdinaryMeasures : SourceRankedConstructorSuppliersTargets.ActualPrimaryOrdinaryMeasures := by
  intro n arity symbols S hc table rank hrank Gamma f base r hq h
  have hs := primaryOrdinaryShape h
  have hr := primaryConstructorRank table rank hrank h
  have hb := primaryConstructorBaseCodes hc h hq
  obtain ⟨rho,r⟩ := r
  cases r with
  | ordinary g base' => exact ⟨g,base',rfl,Option.some.inj hr,hb⟩
  | var => cases hs
  | lam => cases hs
  | app => cases hs
  | bottom => cases hs
  | numbered => cases hs

theorem actualPrimaryNumberedMeasures : SourceRankedConstructorSuppliersTargets.ActualPrimaryNumberedMeasures := by
  intro n arity symbols S hc table rank hrank Gamma k f tau base types extras r hq h
  have hl := primaryLabel h
  have hr := primaryConstructorRank table rank hrank h
  have hb := primaryConstructorBaseCodes hc h hq
  have he := primaryConstructorExtraCodes hc h hq
  obtain ⟨rho,r⟩ := r
  have ht : tau = rho := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
    (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma _ _ h)
  cases ht
  cases r with
  | numbered l g tau base' types' extras' =>
    have hk : l = k := Option.some.inj hl.symm
    subst l
    exact ⟨g,base',types',extras',rfl,Option.some.inj hr,hb,he⟩
  | var => cases hl
  | lam => cases hl
  | app => cases hl
  | bottom => cases hl
  | ordinary => cases hl
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresProof
