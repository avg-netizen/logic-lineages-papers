module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedFiniteUniverse
open NumberedLeastCodeRepresentative SourceBottomSpineComputabilitySupportProof

theorem actualComputabilityLeast : SourceComputabilityLeastTargets.ActualComputabilityLeast := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau
  induction tau with
  | ground =>
    intro value h
    exact h.2
  | arrow sigma tau ihs iht =>
    intro value h
    have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
      (fun x => x ∈ leastSet scalar context) context (.arrow sigma tau) value h
    obtain ⟨f,hf,hrep⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed (.arrow sigma tau) value htyped
    have htype := NumberedUniverseOperationsProof.rootType
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) f hf
    have hsigma := NumberedUniverseOperationsProof.arrowDomain (fun t => t ∈ ctx.1.2) hclosed sigma tau htype
    have hbottom : InUniverse ctx.1.1 ctx.1.2 (AuxTerm.bottom (Symbol := Fin n) (arity := arity) (Gamma := Gamma) sigma) :=
      ⟨hsigma,trivial⟩
    have hca := SourceBottomSpineComputabilityProof.actualBottomComputable
      n arity Gamma context ctx scalar hc hclosed hcal sigma hsigma
    have hi := SourceComputabilityArrowLeastProof.actualConditionalArrowLeast
      n arity Gamma context ctx scalar hc hclosed hcal sigma tau f (.bottom sigma) hf hbottom
      iht (hrep.symm ▸ h) hca
    exact hrep ▸ hi

theorem actualComputabilityAccessible : SourceComputabilityLeastTargets.ActualComputabilityAccessible := by
  intro n arity Gamma context ctx scalar hc hclosed hcal tau value h
  exact (PositiveArithmeticAccessibilityProof.leastImpliesAccessibility scalar context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcal value
    (actualComputabilityLeast n arity Gamma context ctx scalar hc hclosed hcal tau value h)).2

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastProof
