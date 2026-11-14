module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
open TwoSol20261113.CalibratedPrimary.Membership
/-- Original per-type order: cases then recursor. -/
def caseStep : Program 2 := consOf (pairOf (constant 2 2) (.projection 0))
  (consOf (pairOf (constant 2 3) (.projection 0)) (.projection 1))
def casesRecursors : Program 1 := InternalRawListRecursion.listRec (constant 0 0) caseStep
/-- Row inputs [type-list,sigma], preserving tau order. -/
def appStep : Program 3 := consOf (pairOf (constant 3 4)
  (pairOf (.projection 2) (.projection 0))) (.projection 1)
def appRow : Program 2 := InternalRawListRecursion.listRec (constant 1 0) appStep
/-- Outer step [sigma,tail-rows,original-types]. -/
def appsStep : Program 3 := .composition InternalApplicationValidityStackAppend.append
  ![.composition appRow ![.projection 2,.projection 0],.projection 1]
def applications : Program 1 := .composition
  (InternalRawListRecursion.listRec (constant 1 0) appsStep) ![.projection 0,.projection 0]
def rankedStep : Program 2 := consOf (pairOf (constant 2 5) (.projection 0)) (.projection 1)
def rankedHeads : Program 1 := InternalRawListRecursion.listRec (constant 0 0) rankedStep
/-- Inputs [symbols,types], literal rawHeadWindow concatenation. -/
def rawWindow : Program 2 :=
  consOf (pairOf (constant 2 0) (constant 2 0))
    (consOf (pairOf (constant 2 1) (constant 2 0))
      (.composition InternalApplicationValidityStackAppend.append
        ![.composition casesRecursors (fun _ : Fin 1 => .projection 1),
          .composition InternalApplicationValidityStackAppend.append
            ![.composition applications (fun _ : Fin 1 => .projection 1),
              .composition rankedHeads (fun _ : Fin 1 => .projection 0)]]))
/-- Filter inputs [candidate,tail-result,symbols,types], no sorting or deduplication. -/
def filterStep (n : Nat) (arity : Fin n → Nat) : Program 4 :=
  InternalAcceptance.branch (.composition (OriginalHeadWindow.window n arity) ![.projection 0,.projection 2,.projection 3])
    (.projection 1) (consOf (.projection 0) (.projection 1))
def filterHeads (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  InternalRawListRecursion.listRec (constant 2 0) (filterStep n arity)
def sourceHeads (n : Nat) (arity : Fin n → Nat) : Program 2 :=
  .composition (filterHeads n arity) ![rawWindow,.projection 0,.projection 1]
def member (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  .composition contains ![.composition (sourceHeads n arity) ![.projection 1,.projection 2],.projection 0]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads
