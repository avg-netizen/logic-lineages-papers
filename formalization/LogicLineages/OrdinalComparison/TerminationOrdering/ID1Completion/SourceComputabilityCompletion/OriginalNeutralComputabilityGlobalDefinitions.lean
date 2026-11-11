module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobal
open Source UniformCertificateCompletion

/-- Every finite source window uses the SAME selected source/computability
pair, retaining application constructors, source-certificate successors,
all-finite-type neutral expansion and actual variable C. The runtime Gamma
is never an external selector or a fixed decoded environment. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let src := GlobalSourcePackage.source r
  let comp := GlobalSourcePackage.computability r
  OriginalApplicationComputability.AcceptedOutputNonLambda comp context ∧
    OriginalApplicationComputability.AcceptedApplicationComputable comp context ∧
    OriginalNeutralExpansion.ApplicationSuccessorComputability src comp context ∧
    OriginalNeutralExpansion.NeutralComputabilityExpansion src comp context ∧
    OriginalVariableComputability.VariableComputable src comp context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobal
