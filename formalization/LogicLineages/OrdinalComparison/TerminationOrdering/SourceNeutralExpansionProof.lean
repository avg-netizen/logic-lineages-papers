module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedPrimaryShapes NumberedQuotientApplication
open NumberedQuotientPaths SourceBottomSpineComputabilitySupportProof

theorem actualNeutralComputabilityExpansion : SourceNeutralExpansionTargets.ActualNeutralComputabilityExpansion := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau
  induction tau with
  | ground =>
    intro q hq hn hsucc
    refine ⟨encodedTypedOfTerm n arity Gamma context ctx hc hclosed .ground q hq, ?_⟩
    apply (PositiveArithmeticLeastSetProof.semanticLeastUnfolding scalar context _).mpr
    apply (hcal (fun x => x ∈ leastSet scalar context) _).mpr
    constructor
    · refine ⟨ctx,hc,?_⟩
      exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed Gamma _).mpr
        ⟨⟨.ground,q⟩,hq,rfl⟩
    · intro y hy
      exact (hsucc y hy).2
  | arrow sigma tau ihs iht =>
    intro q hq hn hsucc
    refine ⟨encodedTypedOfTerm n arity Gamma context ctx hc hclosed (.arrow sigma tau) q hq, ?_⟩
    intro u hu
    have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
      (fun x => x ∈ leastSet scalar context) context sigma u hu
    obtain ⟨a,ha,hrep⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed sigma u htyped
    have happgood := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity
      ctx.1.1 ctx.1.2 hclosed Gamma sigma tau q a hq ha
    refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked q a), ?_, ?_⟩
    · rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc sigma tau,
        ← hrep]
      exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2
        hclosed Gamma sigma tau q a hq ha
    · apply iht (.app q a) happgood rfl
      intro y hy
      have hpath := (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc _ y).mp hy
      rcases NumberedNonLambdaPathsProof.actualNonLambdaApplicationPath n arity ctx.1.1 ctx.1.2 hclosed
        (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma tau q a y hq ha hn hpath with hb | ⟨g,hg,hqg,hrest⟩
      · have ht := NumberedUniverseOperationsProof.rootType
          (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) (.app q a) happgood
        rw [hb]
        exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Gamma context ctx scalar hc hclosed hcal tau ht
      · have hcg := hsucc (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩)
          ((SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc _ _).mpr (.step hqg))
        obtain ⟨z,hz,hcz⟩ := hcg.2 u hu
        have hcalc : OrdinaryArithmeticApplication.decodedApplication n arity Gamma context
            (typeNumber sigma) (typeNumber tau) (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩) u =
            some (representativeCode ctx.1.1 ctx.1.2 (applicationPacked g a)) := by
          rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc sigma tau, ← hrep]
          exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau g a hg ha
        have he : z = representativeCode ctx.1.1 ctx.1.2 (applicationPacked g a) := Option.some.inj (hz.symm.trans hcalc)
        subst z
        rcases hrest with he | hr
        · exact he ▸ hcz
        · exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar hc hclosed hcal
            tau _ y hcz ((SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc _ y).mpr hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionProof
