module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathTargets
open Source UniformCertificateCompletion OriginalSourceNeutralApplicationPath

/-- The actual original source certificate is a positive path. Only its
first edge receives the non-lambda application's bottom/function split;
the exact original suffix to the caller's endpoint is always retained.
All runtime coordinates, window activation, codomain membership, canonical
argument and first-entry witnesses are conclusions, not caller inputs. -/
def ActualOriginalSourceNeutralApplicationPositivePathElimination : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let r := OriginalApplicationSidecar.finalInputs p
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  SourcePositivePaths (OuterSelection.data r.base r.window) r.window r.oldStep
    (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathTargets
