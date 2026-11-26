module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisit
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant arityOf)
open NumberedMultisetNumeric
/-- Same frame tags and count layout as the checked raw scheduler, but the
parent payload retains role/type annotations. No return frame is executed. -/
def work : Program 1 := leftOf (.projection 0)
def results : Program 1 := rightOf (.projection 0)
def frame : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => work)
def rest : Program 1 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => work)
def parent : Program 1 := rightOf frame
def rawJob : Program 1 := rightOf (rightOf parent)
def raw : Program 1 := leftOf rawJob
def parameter : Program 1 := rightOf rawJob
def returnFrame : Program 1 := pairOf (constant 1 1)
  (pairOf parent (pairOf (arityOf raw)
    (.composition OriginalContextInsertion.length (fun _ : Fin 1 => rightOf parameter))))
def expanded : Program 1 := .composition OriginalHereditaryAnnotatedExpansion.expansion
  (fun _ : Fin 1 => parent)
def scheduled : Program 1 := .composition InternalApplicationValidityStackAppend.append
  ![.composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => expanded),
    consOf returnFrame rest]
def step : Program 1 := InternalAcceptance.branch work (.projection 0)
  (InternalAcceptance.branch (leftOf frame) (pairOf scheduled results) (.projection 0))
/-- Forget only annotations, preserving frame tag and literal return counts.
Unknown frame tags are unchanged. -/
def forgetFrame : Program 1 :=
  OriginalTypedDecoder.ifSame (leftOf (.projection 0)) (constant 1 0)
    (pairOf (constant 1 0) (rightOf (rightOf (rightOf (.projection 0)))))
  (OriginalTypedDecoder.ifSame (leftOf (.projection 0)) (constant 1 1)
    (pairOf (constant 1 1) (pairOf
      (rightOf (rightOf (leftOf (rightOf (.projection 0)))))
      (rightOf (rightOf (.projection 0))))) (.projection 0))
def forgetFrameNumber (frame : Nat) : Nat :=
  let tag := (Nat.unpair frame).1
  let payload := (Nat.unpair frame).2
  if tag=0 then Nat.pair 0 (OriginalHereditaryAnnotatedExpansion.forgetNumber payload)
  else if tag=1 then Nat.pair 1 (Nat.pair
    (OriginalHereditaryAnnotatedExpansion.forgetNumber (Nat.unpair payload).1) (Nat.unpair payload).2)
  else frame
def forgetStep : Program 2 := consOf
  (.composition forgetFrame (fun _ : Fin 1 => .projection 0)) (.projection 1)
def forgetAgenda : Program 1 := InternalRawListRecursion.listRec (constant 0 0) forgetStep
def forgetState : Program 1 := pairOf
  (.composition forgetAgenda (fun _ : Fin 1 => work)) results

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisit
