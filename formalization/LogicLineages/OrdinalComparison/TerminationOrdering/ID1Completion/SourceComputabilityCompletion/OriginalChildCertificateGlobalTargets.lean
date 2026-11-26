module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobalTargets
open UniformCertificateCompletion OriginalChildCertificateGlobal

/-- ONE selection precedes every original source context and runtime Gamma.
The entire accepted package and new child/suffix source certificates coexist
at that selection; neither invariant fields nor source semantics are replaced. -/
def ActualOriginalChildCertificateGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ p : GlobalSourcePackage.Inputs,
      RetainedProperties n arity p ∧ CertificateProperties p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobalTargets
