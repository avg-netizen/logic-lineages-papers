module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLift
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep

/-- Prefix the original focus path. The original replacement and root selector
are preserved literally, including beneath lambda binders. -/
def liftCertificate (c : StepCertificate) : StepCertificate :=
  ⟨.appFunction :: c.path,c.replacement,c.root⟩

/-- Application in the ORIGINAL packed-number encoding. Total on all naturals;
no claim of well-typedness is made without the stated original domain. -/
def rawApplication (domain codomain function argument : Nat) : Nat :=
  Nat.pair codomain (Nat.pair 2 (Nat.pair domain
    (Nat.pair (Nat.unpair function).2 (Nat.unpair argument).2)))

/-- Prefix the ORIGINAL encoded position list, retaining the original pair of
replacement and root codes. This is not a new certificate numbering. -/
def liftStep (certificate : Nat) : Nat :=
  Nat.pair (1 + Nat.pair (positionNumber .appFunction) (Nat.unpair certificate).1)
    (Nat.unpair certificate).2

def applicationValue (v : List.Vector Nat 4) : Nat :=
  rawApplication (v.get 0) (v.get 1) (v.get 2) (v.get 3)

def stepValue (v : List.Vector Nat 1) : Nat := liftStep (v.get 0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLift
