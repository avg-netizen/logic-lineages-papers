module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal source constructor: the successor of the original Nat.pair code. -/
def consCode : Program 2 :=
  .composition .succ (fun _ : Fin 1 => InternalPairing.pairing)

/-- Total source head operation; the zero input is not asserted to be a cons. -/
def headCode : Program 1 :=
  .composition InternalUnpair.left (fun _ : Fin 1 => InternalEqualityTest.predecessor)

/-- Total source tail operation; no arbitrary input is assumed canonical. -/
def tailCode : Program 1 :=
  .composition InternalUnpair.right (fun _ : Fin 1 => InternalEqualityTest.predecessor)

/-- The source nil code is zero, with the existing one-for-true convention. -/
def nilTest : Program 1 :=
  LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.zeroTest

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodec
