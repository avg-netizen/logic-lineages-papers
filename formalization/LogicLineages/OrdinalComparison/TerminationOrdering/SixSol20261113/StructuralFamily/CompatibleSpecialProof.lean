module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions ConfinedStructuralInterpretation SourceConstructorIteration ActualOriginalApplication LiteralSpecialApplicationValue LambdaSpineActions ConfinedSubstitution SubstitutionEnvironmentSupport LiteralSpecialApplicationValueProof

theorem successInterpretation : CompatibleSpecialTargets.SuccessInterpretation := by
  intro Symbol inst arity I M hcompat Γ Δ σ q s hs types τ args ha h P ρ η he r hr heq
  exact CompatibleSpecialInductionProof.success M hcompat q.val q.property s hs args ha h r hr heq P ρ η he

theorem failureBottom : CompatibleSpecialTargets.FailureBottom := by
  intro Symbol inst arity I M hcompat Γ Δ σ q s hs types τ args ha h P ρ η he heq
  exact ActualOriginalApplicationInductionProof.failure q.val q.property s args h heq M P ρ (argumentValues args ha M P η)

theorem specialSuccess : CompatibleSpecialTargets.SpecialSuccess := by
  intro Symbol inst arity I M hcompat P types τ q args ha r hr heq
  have happ := CompatibleApplicationProof.fullApplication Symbol inst arity I M hcompat _ _ q P (identity I P) types τ
    (argumentValues args ha M P (identity I P)) rfl
  have hmask := literalIdentityMasks Symbol inst arity I P _ q M (fun {_} _ => false) (fun {_} _ => true)
    types τ (argumentValues args ha M P (identity I P)) rfl
  have hs := successInterpretation Symbol inst arity I M hcompat _ _ _ q
    (fun {_} v => .var v) identityRange types τ args ha rfl P (identity I P) (identity I P)
    (identityAgreement M P (identity I P)) r hr heq
  exact happ.trans (hmask.trans hs.symm)

theorem specialFailure : CompatibleSpecialTargets.SpecialFailure := by
  intro Symbol inst arity I M hcompat P types τ q args ha heq
  have happ := CompatibleApplicationProof.fullApplication Symbol inst arity I M hcompat _ _ q P (identity I P) types τ
    (argumentValues args ha M P (identity I P)) rfl
  have hmask := literalIdentityMasks Symbol inst arity I P _ q M (fun {_} _ => false) (fun {_} _ => true)
    types τ (argumentValues args ha M P (identity I P)) rfl
  have hf := failureBottom Symbol inst arity I M hcompat _ _ _ q
    (fun {_} v => .var v) identityRange types τ args ha rfl P (identity I P) (identity I P)
    (identityAgreement M P (identity I P)) heq
  exact happ.trans (hmask.trans hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialProof
