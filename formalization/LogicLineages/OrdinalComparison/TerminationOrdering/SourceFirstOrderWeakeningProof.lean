module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakeningTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakeningProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax
open NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceComputabilityFormula SourceFirstOrderWeakening
open NumberedQuotientApplication

theorem actualFirstOrderComputabilityReflection : SourceFirstOrderWeakeningTargets.ActualFirstOrderComputabilityReflection := by
  intro n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma hcalOld hcalNew tau
  induction tau with
  | ground =>
    intro _ q hq hC
    exact (SourceGroundWeakeningProof.actualGroundComputabilityWeakening n arity Gamma context ctx scalarOld scalarNew
      hc hclosed sigma hcalOld hcalNew q hq).mpr hC
  | arrow domain tau ihd iht =>
    intro ht q hq hC
    obtain ⟨hd,ht⟩ := ht
    subst domain
    refine ⟨SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity Gamma context ctx hc hclosed (.arrow .ground tau) q hq,?_⟩
    intro u hu
    have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
      (fun x => x ∈ leastSet scalarOld context) context .ground u hu
    obtain ⟨a,ha,he⟩ := SourceBottomSpineComputabilitySupportProof.encodedTypedWitness n arity Gamma context ctx hc hclosed .ground u htyped
    have hca : Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context .ground
        (representativeCode ctx.1.1 ctx.1.2 ⟨.ground,a⟩) := he.symm ▸ hu
    have hwa := (SourceGroundWeakeningProof.actualGroundComputabilityWeakening n arity Gamma context ctx scalarOld scalarNew
      hc hclosed sigma hcalOld hcalNew a ha).mp hca
    have hwq := NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma (sigma :: Gamma) (.arrow .ground tau) q (Renaming.weaken Gamma sigma) hq
    have hwag := NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma (sigma :: Gamma) .ground a (Renaming.weaken Gamma sigma) ha
    have hresult := SourceConditionalLambdaSupportProof.applicationComputable n arity (sigma :: Gamma) context ctx scalarNew hc hclosed
      .ground tau (rename q (Renaming.weaken Gamma sigma)) (rename a (Renaming.weaken Gamma sigma)) hwq hwag hC hwa
    have happ := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity ctx.1.1 ctx.1.2 hclosed Gamma .ground tau q a hq ha
    have hback := iht ht (.app q a) happ hresult
    refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked q a),?_,hback⟩
    rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc .ground tau,← he]
    exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2 hclosed Gamma .ground tau q a hq ha

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFirstOrderWeakeningProof
