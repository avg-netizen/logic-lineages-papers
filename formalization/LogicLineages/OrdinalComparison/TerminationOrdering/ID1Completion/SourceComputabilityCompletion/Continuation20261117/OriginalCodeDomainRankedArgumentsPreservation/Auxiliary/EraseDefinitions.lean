module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.Erase
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport
/-- Auxiliary deletion accumulator is pair(foundFlag,remainingList).
The right fold removes the LAST occurrence exactly once. Actual zero/nonzero
flag branches are explicit; no successful-search oracle is supplied. -/
def flag : Program 3 := leftOf (.projection 1)
def rest : Program 3 := rightOf (.projection 1)
def kept : Program 3 := consOf (.projection 0) rest
def found : Program 3 := pairOf (constant 3 1) rest
def keepFound : Program 3 := pairOf (constant 3 1) kept
def keepAbsent : Program 3 := pairOf (constant 3 0) kept
def step : Program 3 := InternalAcceptance.branch flag
  (InternalAcceptance.branch (sameOf (.projection 0) (.projection 2)) keepAbsent found)
  keepFound
def state : Program 2 := InternalRawListRecursion.listRec (constant 1 0) step
def remaining : Program 2 := rightOf state
def foundFlag : Program 2 := leftOf state
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.Erase
