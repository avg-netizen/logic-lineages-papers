module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax
open NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceComputabilityFormula

theorem actualGroundComputabilityWeakening : SourceGroundWeakeningTargets.ActualGroundComputabilityWeakening := by
  intro n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma hcalOld hcalNew q hq
  have hw : InUniverse ctx.1.1 ctx.1.2 (rename q (Renaming.weaken Gamma sigma)) :=
    NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma (sigma :: Gamma) .ground q (Renaming.weaken Gamma sigma) hq
  have htOld := SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity Gamma context ctx hc hclosed .ground q hq
  have htNew := SourceBottomSpineComputabilitySupportProof.encodedTypedOfTerm n arity (sigma :: Gamma) context ctx hc hclosed .ground
    (rename q (Renaming.weaken Gamma sigma)) hw
  have hm := SourceWeakeningLeastProof.actualScalarLeastWeakening n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma
    hcalOld hcalNew ⟨.ground,q⟩ hq
  constructor
  · intro h
    exact ⟨htNew,hm.mp h.2⟩
  · intro h
    exact ⟨htOld,hm.mpr h.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundWeakeningProof
