module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationTargets
open Source UniformCertificateCompletion OriginalSourceNeutralApplication

/-- The SAME final globally selected source/computability tuple supplies
original Object application inputs at every closed finite source window.
Neither the runtime Gamma nor window/member witnesses are caller inputs.
The body is arbitrary, so the original sourceBody of this SAME tuple is an
immediate specialization. This contract exposes no positive-path endpoint
shape and imposes no premise on a later function reduct. -/
def ActualOriginalSourceNeutralApplicationInputs : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let r := OriginalApplicationSidecar.finalInputs p
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ApplicationInputs (OuterSelection.data r.base r.window) r.window
    (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationTargets
