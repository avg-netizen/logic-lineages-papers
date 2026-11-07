module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

/-- Literal conditional composition, with control, zero branch, other branch. -/
def branch {n : Nat} (control zeroBranch otherBranch : Program n) : Program n :=
  .composition GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons zeroBranch (Fin.cons otherBranch Fin.elim0)))

def constantZero (n : Nat) : Program n := .composition .zero Fin.elim0

/-- Exact-one conjunction. Both inputs are normalized by the existing AST. -/
def conjunction {n : Nat} (p q : Program n) : Program n :=
  branch (GorbowVerifierNormalization.normalize p) (constantZero n)
    (GorbowVerifierNormalization.normalize q)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance
