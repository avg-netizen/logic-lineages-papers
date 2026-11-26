module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeFreshEnvironmentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeComputabilityTransportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeFreshEnvironmentProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceLambdaEnvironment

theorem actualFreshEnvironmentFromComputable : SourceAllTypeFreshEnvironmentTargets.ActualFreshEnvironmentFromComputable := by
  intro n arity Gamma Delta context ctx scalarOld scalarNew sigma hc hclosed hs hcalOld hcalNew theta hg he
  apply SourceLambdaEnvironmentProof.actualFreshEnvironment n arity Gamma Delta context ctx scalarNew sigma
    hc hclosed hs hcalNew theta hg
  intro tau v
  have hC := he tau v
  have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Delta
    (fun x => x ∈ leastSet scalarOld context) context tau _ hC
  obtain ⟨a,ha,_⟩ := SourceBottomSpineComputabilitySupportProof.encodedTypedWitness n arity Delta context ctx hc hclosed tau _ htyped
  have ht : tau ∈ ctx.1.2 := NumberedUniverseOperationsProof.rootType (fun t => t ∈ ctx.1.2)
    (HeadInWindow arity ctx.1.1 ctx.1.2) a ha
  exact (SourceAllTypeComputabilityTransportProof.actualComputabilityWeakening n arity Delta context ctx scalarOld scalarNew
    hc hclosed sigma hcalOld hcalNew tau (theta v) (hg v ht)).mp hC

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceAllTypeFreshEnvironmentProof
