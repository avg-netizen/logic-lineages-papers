module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax
open NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceComputabilityFormula
open NumberedQuotientApplication SourceAllTypeComputabilityTransportSupportProof

theorem actualComputabilitySingleBottom : SourceAllTypeComputabilityTransportTargets.ActualComputabilitySingleBottom := by
  intro n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma hcalOld hcalNew tau
  induction tau with
  | ground =>
    intro q hq
    have heq := singleBottomConfinement ctx.1.1 ctx.1.2 Gamma sigma .ground q hq
    have htOld := SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity Gamma context ctx hc hclosed .ground
      (substitute q (singleSubstitution (.bottom sigma))) heq
    have htNew := SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity (sigma :: Gamma) context ctx hc hclosed .ground q hq
    have hm := SourceSingleBottomLeastProof.actualScalarLeastSingleBottom n arity Gamma context ctx scalarOld scalarNew
      hc hclosed sigma hcalOld hcalNew ⟨.ground,q⟩ hq
    constructor
    · intro h
      exact ⟨htOld,hm.mp h.2⟩
    · intro h
      exact ⟨htNew,hm.mpr h.2⟩
  | arrow domain tau ihd iht =>
    intro q hq
    have heq := singleBottomConfinement ctx.1.1 ctx.1.2 Gamma sigma (.arrow domain tau) q hq
    constructor
    · intro hC
      refine ⟨SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity Gamma context ctx hc hclosed
        (.arrow domain tau) (substitute q (singleSubstitution (.bottom sigma))) heq,?_⟩
      intro u hu
      have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
        (fun x => x ∈ leastSet scalarOld context) context domain u hu
      obtain ⟨a,ha,he⟩ := SourceBottomSpineComputabilitySupportProof.encodedTypedWitness
        n arity Gamma context ctx hc hclosed domain u htyped
      have hca : Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context domain
          (representativeCode ctx.1.1 ctx.1.2 ⟨domain,a⟩) := he.symm ▸ hu
      have hwa := NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ ctx.1.2)
        (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma (sigma :: Gamma) domain a (Renaming.weaken Gamma sigma) ha
      have hwaC : Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalarNew context) context domain
          (representativeCode ctx.1.1 ctx.1.2 ⟨domain,rename a (Renaming.weaken Gamma sigma)⟩) := by
        apply (ihd (rename a (Renaming.weaken Gamma sigma)) hwa).mpr
        rw [NumberedRewriteApplicationBindingProof.weakeningCancellation]
        exact hca
      have hresult := SourceConditionalLambdaSupportProof.applicationComputable n arity (sigma :: Gamma) context ctx scalarNew
        hc hclosed domain tau q (rename a (Renaming.weaken Gamma sigma)) hq hwa hC hwaC
      have happ := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity ctx.1.1 ctx.1.2 hclosed
        (sigma :: Gamma) domain tau q (rename a (Renaming.weaken Gamma sigma)) hq hwa
      have hback := (iht (.app q (rename a (Renaming.weaken Gamma sigma))) happ).mp hresult
      change Computable n arity Gamma (fun x => x ∈ leastSet scalarOld context) context tau
        (representativeCode ctx.1.1 ctx.1.2 (applicationPacked (substitute q (singleSubstitution (.bottom sigma)))
          (substitute (rename a (Renaming.weaken Gamma sigma)) (singleSubstitution (.bottom sigma))))) at hback
      rw [NumberedRewriteApplicationBindingProof.weakeningCancellation] at hback
      refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked (substitute q (singleSubstitution (.bottom sigma))) a),?_,hback⟩
      rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc domain tau,← he]
      exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2 hclosed Gamma
        domain tau (substitute q (singleSubstitution (.bottom sigma))) a heq ha
    · intro hC
      refine ⟨SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity (sigma :: Gamma) context ctx hc hclosed
        (.arrow domain tau) q hq,?_⟩
      intro u hu
      have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity (sigma :: Gamma)
        (fun x => x ∈ leastSet scalarNew context) context domain u hu
      obtain ⟨a,ha,he⟩ := SourceBottomSpineComputabilitySupportProof.encodedTypedWitness
        n arity (sigma :: Gamma) context ctx hc hclosed domain u htyped
      have hca : Computable n arity (sigma :: Gamma) (fun x => x ∈ leastSet scalarNew context) context domain
          (representativeCode ctx.1.1 ctx.1.2 ⟨domain,a⟩) := he.symm ▸ hu
      have hea := singleBottomConfinement ctx.1.1 ctx.1.2 Gamma sigma domain a ha
      have heaC := (ihd a ha).mp hca
      have hresult := SourceConditionalLambdaSupportProof.applicationComputable n arity Gamma context ctx scalarOld
        hc hclosed domain tau (substitute q (singleSubstitution (.bottom sigma)))
        (substitute a (singleSubstitution (.bottom sigma))) heq hea hC heaC
      have happ := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity ctx.1.1 ctx.1.2 hclosed
        (sigma :: Gamma) domain tau q a hq ha
      have hback := (iht (.app q a) happ).mpr hresult
      refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked q a),?_,hback⟩
      rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity (sigma :: Gamma) context ctx hc domain tau,← he]
      exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2 hclosed
        (sigma :: Gamma) domain tau q a hq ha

theorem actualComputabilityWeakening : SourceAllTypeComputabilityTransportTargets.ActualComputabilityWeakening := by
  intro n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma hcalOld hcalNew tau q hq
  have hwq := NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ ctx.1.2)
    (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma (sigma :: Gamma) tau q (Renaming.weaken Gamma sigma) hq
  have h := actualComputabilitySingleBottom n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma
    hcalOld hcalNew tau (rename q (Renaming.weaken Gamma sigma)) hwq
  rw [NumberedRewriteApplicationBindingProof.weakeningCancellation] at h
  exact h.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportProof
