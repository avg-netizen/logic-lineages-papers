module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientApplication
open SourceComputabilityArrowLeastSupportProof

theorem actualConditionalArrowLeast : SourceComputabilityArrowLeastTargets.ActualConditionalArrowLeast := by
  intro n arity Gamma context ctx scalar hc hclosed hcal sigma tau f a hf ha hcod hcf hca
  obtain ⟨z, hz, hcz⟩ := hcf.2 (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩) hca
  rw [applicationCalibration n arity Gamma context ctx hc sigma tau] at hz
  have happ := NumberedNumericApplicationProof.canonicalApplicationCalibration
    n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau f a hf ha
  have he : representativeCode ctx.1.1 ctx.1.2 (applicationPacked f a) = z :=
    Option.some.inj (happ.symm.trans hz)
  have hiz : representativeCode ctx.1.1 ctx.1.2 (applicationPacked f a) ∈ leastSet scalar context :=
    he.symm ▸ hcod z hcz
  have hencoded := (PositiveArithmeticAccessibilityProof.leastImpliesAccessibility scalar context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcal _ hiz).2
  have hactual : Acc (fun successor source =>
      QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2 source successor)
      (representativeCode ctx.1.1 ctx.1.2 (applicationPacked f a)) :=
    Subrelation.accessible (fun {y x} h => (relationCalibration n arity Gamma context ctx hc x y).mpr h) hencoded
  have hinverse := NumberedInverseApplicationAccessibilityProof.actualInverseApplicationAccessibility
    n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma tau f a hf ha hactual
  have hacc : Acc (fun successor source => encodedR n arity Gamma context source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩) :=
    Subrelation.accessible (fun {y x} h => (relationCalibration n arity Gamma context ctx hc x y).mp h) hinverse
  have hcarrier : encodedScalar n arity Gamma context
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩) := by
    refine ⟨ctx, hc, ?_⟩
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed Gamma _).mpr
      ⟨⟨.arrow sigma tau,f⟩, hf, rfl⟩
  exact (PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalar context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcal
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity Gamma context ⟨ctx,hc,hclosed⟩) _).mpr
    ⟨hcarrier, hacc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastProof
