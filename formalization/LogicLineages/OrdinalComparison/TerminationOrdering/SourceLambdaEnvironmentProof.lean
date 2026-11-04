module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative SourceLambdaEnvironment

theorem actualArgumentEnvironment : SourceLambdaEnvironmentTargets.ActualArgumentEnvironment := by
  intro n arity Gamma Delta context ctx P sigma theta a hg ha he hca
  constructor
  · intro tau v ht
    cases v with
    | here => exact ha
    | there v => exact hg v ht
  · intro tau v
    cases v with
    | here => exact hca
    | there v => exact he _ v

theorem actualFreshEnvironment : SourceLambdaEnvironmentTargets.ActualFreshEnvironment := by
  intro n arity Gamma Delta context ctx scalar sigma hc hclosed hs hcal theta hg he
  refine ⟨NumberedUniverseBindingProof.liftGood _ _ theta hg,?_⟩
  intro tau v
  cases v with
  | here =>
    exact SourceInertSpineComputabilityProof.actualVariableComputable n arity (sigma :: Delta)
      context ctx scalar hc hclosed hcal sigma .here hs
  | there v => exact he _ v

theorem actualExtendedBetaIdentity : SourceLambdaEnvironmentTargets.ActualExtendedBetaIdentity := by
  intro Symbol arity Gamma Delta sigma tau theta body a
  rw [NumberedSubstitutionCompositionProof.actualTermSubstitutionComposition]
  have he : (fun {upsilon : Ty} (v : Variable (sigma :: Gamma) upsilon) =>
      substitute (liftSubstitution theta v) (singleSubstitution a)) = (fun {upsilon : Ty} (v : Variable (sigma :: Gamma) upsilon) => extend theta a v) := by
    funext upsilon v
    cases v with
    | here => rfl
    | there v =>
      exact NumberedRewriteApplicationBindingProof.weakeningCancellation Symbol arity Delta sigma _ (theta v) a
  rw [he]

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironmentProof
