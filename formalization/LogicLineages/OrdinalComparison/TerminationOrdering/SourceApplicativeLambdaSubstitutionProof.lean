module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths
open OrdinaryArithmeticCarrier PositiveArithmeticLeastSet SourceLambdaEnvironment

theorem actualApplicativeLambdaSubstitution : SourceApplicativeLambdaSubstitutionTargets.ActualApplicativeLambdaSubstitution := by
  intro n arity Gamma Delta context ctx scalarOld scalarFresh sigma tau hc hclosed hold hfresh theta hg he hwe body hl hfrag
  have hb : InUniverse ctx.1.1 ctx.1.2 body := ⟨hl.1.2.2,hl.2⟩
  obtain ⟨hlift,helift⟩ := SourceLambdaEnvironmentProof.actualFreshEnvironment n arity Gamma Delta
    context ctx scalarFresh sigma hc hclosed hl.1.2.1 hfresh theta hg hwe
  have hcb := SourceApplicativeSubstitutionProof.actualApplicativeComputableSubstitution n arity
    (sigma :: Gamma) (sigma :: Delta) context ctx scalarFresh hc hclosed hfresh
    (liftSubstitution theta) hlift helift tau body hb hfrag
  have hencoded := SourceComputabilityLeastProof.actualComputabilityAccessible n arity (sigma :: Delta)
    context ctx scalarFresh hc hclosed hfresh tau _ hcb
  have hacc : Acc (fun successor source => PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (sigma :: Delta)) source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute body (liftSubstitution theta)⟩) :=
    Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (sigma :: Delta) context ctx hc x y).mpr h) hencoded
  have hls := NumberedUniverseBindingProof.actualSubstitution (Fin n) arity
    (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma Delta (.arrow sigma tau) (.lam body) theta hl hg
  apply SourceConditionalLambdaProof.actualConditionalLambdaComputability n arity Delta context ctx scalarOld
    hc hclosed hold sigma tau (substitute body (liftSubstitution theta)) hls hacc
  intro a ha hca
  obtain ⟨harg,hearg⟩ := SourceLambdaEnvironmentProof.actualArgumentEnvironment n arity Gamma Delta
    context ctx (fun x => x ∈ leastSet scalarOld context) sigma theta a hg ha he hca
  have hinstance := SourceApplicativeSubstitutionProof.actualApplicativeComputableSubstitution n arity
    (sigma :: Gamma) Delta context ctx scalarOld hc hclosed hold (extend theta a) harg hearg tau body hb hfrag
  rw [SourceLambdaEnvironmentProof.actualExtendedBetaIdentity (Fin n) arity Gamma Delta sigma tau theta body a]
  exact hinstance

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionProof
