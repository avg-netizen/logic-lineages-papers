module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentProof
open Source Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment

theorem restrictionIdentity : TypedValueEnvironmentTargets.RestrictionIdentity := by
  intro Symbol inst arity I Γ P ρ
  funext τ v
  exact (family I τ).restrictIdentity P (ρ v)

theorem restrictionComposition : TypedValueEnvironmentTargets.RestrictionComposition := by
  intro Symbol inst arity I Γ P Q R h k ρ
  funext τ v
  exact (family I τ).restrictComposition P Q R h k (ρ v)

theorem restrictionMonotone : TypedValueEnvironmentTargets.RestrictionMonotone := by
  intro Symbol inst arity I Γ P Q h ρ η hρη τ v
  exact (family I τ).restrictMonotone P Q h (ρ v) (η v) (hρη v)

theorem extensionMonotone : TypedValueEnvironmentTargets.ExtensionMonotone := by
  intro Symbol inst arity I Γ σ P a b ρ η hab hρη τ v
  cases v with
  | here => exact hab
  | there v => exact hρη v

theorem extensionRestriction : TypedValueEnvironmentTargets.ExtensionRestriction := by
  intro Symbol inst arity I Γ σ P Q h a ρ
  funext τ v
  cases v <;> rfl

theorem identityTransport : TypedValueEnvironmentTargets.IdentityTransport := by
  intro Symbol inst arity I P Q h
  funext τ v
  apply RecursiveNaturalDomainsProof.layerViewInjective I τ Q
  change layerView I τ Q (RecursiveNaturalDomains.weaken h (LiteralVariableValueProof.variableValue v)) =
    layerView I τ Q (LiteralVariableValueProof.variableValue (LiteralVariableValue.extendVariables I.context Q.val P.val h v))
  rw [RecursiveNaturalDomainsProof.layerViewWeaken]
  simp only [LiteralVariableValueProof.variableValue,RecursiveNaturalDomainsProof.layerViewFold]
  apply Subtype.ext
  exact LiteralVariableValueProof.variableWeakening Symbol inst arity I τ P Q h v

theorem reindexRestriction : TypedValueEnvironmentTargets.ReindexRestriction := by
  intro Symbol inst arity I Γ Δ P Q h r ρ
  rfl

theorem reindexLift : TypedValueEnvironmentTargets.ReindexLift := by
  intro Symbol inst arity I Γ Δ σ P r a ρ
  funext τ v
  cases v <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentProof
