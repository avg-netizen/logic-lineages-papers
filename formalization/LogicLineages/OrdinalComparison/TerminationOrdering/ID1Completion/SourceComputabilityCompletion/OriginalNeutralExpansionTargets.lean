module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansionTargets
open Source UniformCertificateCompletion OriginalNeutralExpansion

/-- SAME global original selection before every finite source window and
runtime Gamma, with all original source certificate consumers retained. -/
def ActualOriginalFinalApplicationSuccessorComputability : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ApplicationSuccessorComputability (GlobalSourcePackage.source r)
    (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

/-- Finite-type induction concludes genuine original C at the SAME selected
source/computability pair. This is not the closed all-term accessibility
statement and does not discharge lambda/substitution or constructor cases. -/
def ActualOriginalFinalNeutralComputabilityExpansion : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  NeutralComputabilityExpansion (GlobalSourcePackage.source r)
    (GlobalSourcePackage.computability r)
    (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralExpansionTargets
