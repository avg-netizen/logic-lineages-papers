module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityTargets
open Source UniformCertificateCompletion OriginalApplicationComputability

/-- The SAME leaf refinement and unchanged final pipeline used by the child
certificate and suffix consumers. One original calibrated input precedes
every finite source window and internally encoded ambient Gamma. -/
def ActualOriginalFinalAcceptedOutputNonLambda : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  AcceptedOutputNonLambda (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

/-- The actual source computability constructor is retained at that SAME
final tuple. No existentially different calibrated presentation, supplied
internal correctness field or new arithmetic inference rule is admitted. -/
def ActualOriginalFinalAcceptedApplicationComputable : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  AcceptedApplicationComputable (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityTargets
