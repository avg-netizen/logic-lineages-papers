module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
def raw : Program 2 := .projection 0
def tailOption : Program 2 := .projection 1
def annotation : Program 2 := leftOf (rightOf raw)
def child : Program 2 := leftOf (rightOf (rightOf raw))
def entry : Program 2 := pairOf annotation child
def tailList : Program 2 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => tailOption)
def prepend : Program 2 := .composition InternalListCodec.consCode ![entry,tailList]
def consCase : Program 2 := InternalAcceptance.branch tailOption (constant 2 0) (succOf prepend)
def choose (tag : Nat) (yes no : Program 2) : Program 2 :=
  InternalAcceptance.branch (sameOf (leftOf raw) (constant 2 tag)) no yes
/-- Inner Option(List entries): None=0, Some []=1. Non-spines fail. -/
def step : Program 2 := choose 6 (constant 2 1) (choose 7 consCase (constant 2 0))
def tailAnswer : Program 2 := .composition InternalRawListRecursion.lookup ![constant 2 1,.projection 1]
/-- Actual original entriesRecombine always returns outer Some; consumes answer1. -/
def recombine : Program 2 := succOf (.composition step ![raw,tailAnswer])
def semanticStep {n : Nat} (c : NumberedAuxiliaryCoding.Code (Fin n))
    (tail : Option (List (Source.Ty × NumberedAuxiliaryCoding.Code (Fin n)))) :
    Option (List (Source.Ty × NumberedAuxiliaryCoding.Code (Fin n))) :=
  match c with
  | .argumentsNil => some []
  | .argumentsCons tau q _ => tail.map (fun entries => (tau,q)::entries)
  | _ => none
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer
