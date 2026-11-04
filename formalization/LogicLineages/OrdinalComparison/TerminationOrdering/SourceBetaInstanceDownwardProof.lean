module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceBetaInstanceDownwardTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceBetaInstanceDownwardProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedUniverseBindingTargets

theorem actualBetaInstanceDownward : SourceBetaInstanceDownwardTargets.ActualBetaInstanceDownward := by
  intro n arity Gamma context ctx scalar hc hclosed hcal sigma tau body body' a hb hb' ha hp hcomp
  have hgood : GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) (singleSubstitution a) := by
    intro upsilon v ht
    cases v with
    | here => exact ha
    | there v => exact ⟨ht,trivial⟩
  have hsub := NumberedQuotientSubstitutionProof.actualPositiveQuotientSubstitution n arity ctx.1.1 ctx.1.2
    hclosed (NumberedCopyCertificate.tableAbove ctx.2) (sigma::Gamma) Gamma (singleSubstitution a)
    ⟨tau,body⟩ ⟨tau,body'⟩ hb hb' hgood hp
  rcases hsub with he | hpath
  · exact he ▸ hcomp
  · have hencoded := (SourceComputabilityArrowLeastSupportProof.relationCalibration
      n arity Gamma context ctx hc _ _).mpr hpath
    exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar
      hc hclosed hcal tau _ _ hcomp hencoded

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceBetaInstanceDownwardProof
