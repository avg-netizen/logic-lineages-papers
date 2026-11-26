module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateDefinitions
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep
/-- Original function position only; argument and runtime context are unchanged. -/
def liftCertificate (child : StepCertificate) : StepCertificate :=
 ⟨.appFunction :: child.path, child.replacement, child.root⟩
def liftStep (certificate : Nat) : Nat :=
 Nat.pair (1 + Nat.pair (positionNumber .appFunction) (Nat.unpair certificate).1) (Nat.unpair certificate).2
def stripStep (certificate : Nat) : Nat :=
 Nat.pair (Nat.unpair ((Nat.unpair certificate).1 - 1)).2 (Nat.unpair certificate).2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionCertificateDefinitions
