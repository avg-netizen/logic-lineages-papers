module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityDownwardTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityDownwardProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientApplication
open SourceBottomSpineComputabilitySupportProof SourceComputabilityArrowLeastSupportProof

theorem actualComputabilityDownward : SourceComputabilityDownwardTargets.ActualComputabilityDownward := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau
  induction tau with
  | ground =>
    intro x y hx hxy
    obtain ⟨q,hq,hrep⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed .ground x hx.1
    have hp := (relationCalibration n arity Gamma context ctx hc x y).mp hxy
    rw [← hrep] at hp
    obtain ⟨r,hr,hre,ht⟩ := NumberedInverseApplicationAccessibilityProof.actualTypedSuccessorWitness
      n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2) Gamma .ground q y hq hp
    refine ⟨hre ▸ encodedTypedOfTerm n arity Gamma context ctx hc hclosed .ground r hr, ?_⟩
    have hbody := (PositiveArithmeticLeastSetProof.semanticLeastUnfolding scalar context x).mp hx.2
    exact ((hcal (fun z => z ∈ leastSet scalar context) x).mp hbody).2 y hxy
  | arrow sigma tau ihs iht =>
    intro x y hx hxy
    obtain ⟨f,hf,hrep⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed (.arrow sigma tau) x hx.1
    have hp := (relationCalibration n arity Gamma context ctx hc x y).mp hxy
    rw [← hrep] at hp
    obtain ⟨g,hg,hre,ht⟩ := NumberedInverseApplicationAccessibilityProof.actualTypedSuccessorWitness
      n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2) Gamma (.arrow sigma tau) f y hf hp
    refine ⟨hre ▸ encodedTypedOfTerm n arity Gamma context ctx hc hclosed (.arrow sigma tau) g hg, ?_⟩
    intro u hu
    have hutyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
      (fun z => z ∈ leastSet scalar context) context sigma u hu
    obtain ⟨a,ha,hua⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed sigma u hutyped
    obtain ⟨z,hz,hcz⟩ := hx.2 u hu
    rw [applicationCalibration n arity Gamma context ctx hc sigma tau, ← hrep, ← hua] at hz
    have hfa := NumberedNumericApplicationProof.canonicalApplicationCalibration
      n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau f a hf ha
    have hez : representativeCode ctx.1.1 ctx.1.2 (applicationPacked f a) = z :=
      Option.some.inj (hfa.symm.trans hz)
    have hfg := NumberedQuotientApplicationPathsProof.actualPositiveFunctionApplication
      n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma tau f g a hf hg ha
      (hre.symm ▸ hp)
    have hencoded := (relationCalibration n arity Gamma context ctx hc
      (representativeCode ctx.1.1 ctx.1.2 (applicationPacked f a))
      (representativeCode ctx.1.1 ctx.1.2 (applicationPacked g a))).mpr hfg
    refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked g a), ?_,
      iht _ _ (hez.symm ▸ hcz) hencoded⟩
    rw [applicationCalibration n arity Gamma context ctx hc sigma tau, ← hre, ← hua]
    exact NumberedNumericApplicationProof.canonicalApplicationCalibration
      n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau g a hg ha

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityDownwardProof
