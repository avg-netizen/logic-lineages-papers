module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceInertSpineComputabilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceInertSpineComputabilityProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedInertSpine NumberedQuotientApplication
open SourceBottomSpineComputabilitySupportProof

theorem actualInertSpineLeast : SourceInertSpineComputabilityTargets.ActualInertSpineLeast := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau q hq hb
  have hactual := NumberedInertSpineAccessibilityProof.actualQuotientInertAccessibility n arity
    ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2) Gamma tau q hq hb
  have hacc : Acc (fun successor source => encodedR n arity Gamma context source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) :=
    Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc x y).mp h) hactual
  have hcarrier : encodedScalar n arity Gamma context (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) := by
    refine ⟨ctx,hc,?_⟩
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed Gamma _).mpr
      ⟨⟨tau,q⟩,hq,rfl⟩
  exact (PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalar context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcal
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity Gamma context ⟨ctx,hc,hclosed⟩) _).mpr
    ⟨hcarrier,hacc⟩

theorem actualInertSpineComputable : SourceInertSpineComputabilityTargets.ActualInertSpineComputable := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau
  induction tau with
  | ground =>
    intro q hq hb
    exact ⟨encodedTypedOfTerm n arity Gamma context ctx hc hclosed .ground q hq,
      actualInertSpineLeast n arity Gamma context ctx scalar hc hclosed hcal .ground q hq hb⟩
  | arrow sigma tau ihs iht =>
    intro q hq hb
    refine ⟨encodedTypedOfTerm n arity Gamma context ctx hc hclosed (.arrow sigma tau) q hq, ?_⟩
    intro u hu
    have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
      (fun x => x ∈ leastSet scalar context) context sigma u hu
    obtain ⟨a,ha,hrep⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed sigma u htyped
    have happgood := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity
      ctx.1.1 ctx.1.2 hclosed Gamma sigma tau q a hq ha
    refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked q a), ?_, iht (.app q a) happgood hb⟩
    rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc sigma tau,
      ← hrep]
    exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2
      hclosed Gamma sigma tau q a hq ha

theorem actualVariableComputable : SourceInertSpineComputabilityTargets.ActualVariableComputable := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau v ht
  exact actualInertSpineComputable n arity Gamma context ctx scalar hc hclosed hcal tau
    (.var v) ⟨ht,trivial⟩ trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceInertSpineComputabilityProof
