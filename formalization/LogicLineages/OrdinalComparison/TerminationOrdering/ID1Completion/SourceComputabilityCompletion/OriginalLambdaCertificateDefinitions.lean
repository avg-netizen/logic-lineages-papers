module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificate
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep

/-- Add the original lambda position, without changing the replacement or
root selector. The child is checked in sigma::Gamma, not in Gamma. -/
def liftCertificate (child : StepCertificate) : StepCertificate :=
  ⟨.lam :: child.path,child.replacement,child.root⟩

/-- Prefix the original numeric position-list encoding. This is the existing
stepCertificateNumber numbering, not a new encoding of certificates. -/
def liftStep (certificate : Nat) : Nat :=
  Nat.pair (1 + Nat.pair (positionNumber .lam) (Nat.unpair certificate).1)
    (Nat.unpair certificate).2

/-- Remove one encoded position from the original certificate. This total
function has explicit behavior on malformed inputs; its successful use below
is justified by the SAME supplied certificate decoding to a lambda path. -/
def stripStep (certificate : Nat) : Nat :=
  Nat.pair (Nat.unpair ((Nat.unpair certificate).1 - 1)).2
    (Nat.unpair certificate).2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificate
