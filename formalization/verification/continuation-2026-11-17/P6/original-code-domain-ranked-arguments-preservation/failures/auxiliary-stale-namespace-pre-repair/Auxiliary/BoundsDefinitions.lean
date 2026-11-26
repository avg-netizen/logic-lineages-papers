module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport
/-- Exact Nat maximum: select the second input precisely when first<second. -/
def maximum : Program 2 := InternalAcceptance.branch InternalLessThan.ltTest (.projection 0) (.projection 1)
/-- Original mergeBounds on the original Nat.pair encoding, for arbitrary inputs. -/
def merge : Program 2 := pairOf
  (addOf (leftOf (.projection 0)) (leftOf (.projection 1)))
  (.composition maximum ![rightOf (.projection 0),rightOf (.projection 1)])
/-- Original ordered foldr, with encoded (0,0) base. -/
def collect : Program 1 := InternalRawListRecursion.listRec (constant 0 0) merge
/-- Root contribution: list constructors contribute zero, numbered contributes
(1,k), all other admitted constructors (1,0). Actual decoder failure returns0. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination
