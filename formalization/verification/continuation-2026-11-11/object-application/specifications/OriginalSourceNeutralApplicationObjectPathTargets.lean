module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathTargets
open Source UniformCertificateCompletion OriginalSourceNeutralApplicationObjectPath

/-- Preserve the actual original source/domain/application/non-lambda inputs
and classify only the first edge of the supplied positive source certificate.
The function case additionally reconstructs the original Object application
at that first vertex, with its requested argument Object unchanged. All
coordinates and new Objects are conclusions bound internally at the SAME
finalInputs tuple; no source-certificate or computability bridge is assumed. -/
def ActualOriginalSourceNeutralApplicationObjectPositivePathElimination : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let r := OriginalApplicationSidecar.finalInputs p
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ObjectSourcePositivePaths (OuterSelection.data r.base r.window) r.window r.oldStep
    (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathTargets
