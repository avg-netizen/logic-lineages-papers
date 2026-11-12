module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitScheduler
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open OriginalHereditaryExpansion
/-- Visit and return tags are disjoint. Return metadata retains the parent job,
raw-child boundary and deletion count; assembly is deliberately unsupported. -/
def visitNumber (job : Nat) := Nat.pair 0 job
def returnNumber (job childCount deletionCount : Nat) :=
  Nat.pair 1 (Nat.pair job (Nat.pair childCount deletionCount))
def stateNumber (work results : List Nat) := Nat.pair
  (NumberedMultisetNumeric.numbersNumber work) (NumberedMultisetNumeric.numbersNumber results)
def tagStep : Program 2 := OriginalHereditaryExpansion.consOf (pairOf (constant 2 0) (.projection 0)) (.projection 1)
def tagVisits : Program 1 := InternalRawListRecursion.listRec (constant 0 0) tagStep

def work : Program 1 := leftOf (.projection 0)
def results : Program 1 := rightOf (.projection 0)
def frame : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => work)
def rest : Program 1 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => work)
def job : Program 1 := rightOf frame
def raw : Program 1 := leftOf job
def parameter : Program 1 := rightOf job
def returnFrame : Program 1 := pairOf (constant 1 1)
  (pairOf job (pairOf (arityOf raw)
    (.composition OriginalContextInsertion.length (fun _ : Fin 1 => rightOf parameter))))
def expanded : Program 1 :=
  .composition OriginalHereditaryExpansion.expansion ![raw,parameter]
def scheduled : Program 1 :=
  .composition InternalApplicationValidityStackAppend.append
    ![.composition tagVisits (fun _ : Fin 1 => expanded),OriginalHereditaryExpansion.consOf returnFrame rest]
def visitStep : Program 1 := pairOf scheduled results
/-- Empty work and every non-visit frame preserve the ENTIRE original state.
Only visits schedule work. No return assembly, recursive evaluator or fuel. -/
def step : Program 1 := InternalAcceptance.branch work (.projection 0)
  (InternalAcceptance.branch (leftOf frame) visitStep (.projection 0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitScheduler
