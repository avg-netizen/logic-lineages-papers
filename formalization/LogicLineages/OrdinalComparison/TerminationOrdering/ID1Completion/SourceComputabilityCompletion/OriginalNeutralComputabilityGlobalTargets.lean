module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalTargets
open UniformCertificateCompletion OriginalChildCertificateGlobal OriginalNeutralComputabilityGlobal

/-- Preserve the entire previous calibrated package and literal child/suffix
certificate consumers at ONE original selection, now adding genuine neutral
and variable computability at every finite type. This supporting theorem does
not assert lambda/substitution, numbered constructors or all-term accessibility. -/
def ActualOriginalNeutralComputabilityGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ p : GlobalSourcePackage.Inputs,
      RetainedProperties n arity p ∧ CertificateProperties p ∧ Properties n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalTargets
