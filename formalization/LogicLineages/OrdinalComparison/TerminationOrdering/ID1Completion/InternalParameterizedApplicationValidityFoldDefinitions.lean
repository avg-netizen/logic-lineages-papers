module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFold
open LogicLineages.ComputabilityKnowledge GorbowPRProgram

/-- EVERY original tag-two root opens, regardless of node acceptance. Moving
node into this opening guard would incorrectly use the old leaf on rejected
applications. The existing fold itself still checks the original tag. -/
def openingGuardP : Program 2 := InternalLessThan.constantOne 2

/-- Non-application roots normalize the old binary leaf on the WHOLE original
packed input and unchanged p. Arbitrary non-one leaf outputs become zero. -/
def leafP (oldLeaf : Program 2) : Program 2 :=
  GorbowVerifierNormalization.normalize oldLeaf

/-- Combine inputs are [d,e,functionOutput,argumentOutput,p]. The node test
receives precisely the original codomain e and the SAME parameter p. -/
def nodeAtP (node : Program 2) : Program 5 :=
  .composition node ![.projection 1, .projection 4]

/-- Exact-one conjunction, including arbitrary non-Boolean node/child values.
The function output precedes the argument output. Node rejection returns zero
at combine; it does not change which roots the original fold opens. -/
def combineP (node : Program 2) : Program 5 :=
  InternalAcceptance.conjunction (nodeAtP node)
    (InternalAcceptance.conjunction (.projection 2) (.projection 3))

/-- The existing parameterized RESULT fold at its original 2*payload+1 fuel.
This is a different AST from the older Boolean work stack at payload+1 fuel.
Only semantic calibration to original validity is claimed, never AST identity. -/
def validatorP (node oldLeaf : Program 2) : Program 2 :=
  InternalParameterizedApplicationResultStack.foldP openingGuardP (leafP oldLeaf)
    (combineP node)

/-- Original target validity has no universe filter. -/
def targetP (oldTarget : Program 2) : Program 2 :=
  validatorP (InternalLessThan.constantOne 2) oldTarget

/-- The original source universe checks codomain membership at applications
and delegates whole non-application roots to the old source leaf. -/
def universeP (oldSource member : Program 2) : Program 2 :=
  validatorP member oldSource

/-- The concrete conjunction gives internal source-to-target acceptance
without any semantic calibration or assumed source-validity implication. -/
def sourceP (oldSource oldTarget member : Program 2) : Program 2 :=
  InternalAcceptance.conjunction (targetP oldTarget) (universeP oldSource member)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFold
