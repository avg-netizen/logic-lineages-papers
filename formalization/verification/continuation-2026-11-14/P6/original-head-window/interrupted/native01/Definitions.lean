module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
open TwoSol20261113.CalibratedPrimary.Membership
/-- Actual finite arity table; raw ranked payload is Fin.val. -/
def arityAt (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  .composition InternalRawListRecursion.lookup
    ![.projection 0,constant 3 (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))]
def typeMember (p : Program 3) : Program 3 := .composition contains ![.projection 2,p]
def applicationArguments : Program 3 :=
  InternalAcceptance.conjunction
    (typeMember (succOf (.projection 0))) (typeMember (InternalApplicationCertificateConstructors.leftOf (.projection 0)))
def rankedArguments (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  InternalAcceptance.branch (arityAt n arity) (constant 3 1) (typeMember (constant 3 0))
def branchWindow (n : Nat) (arity : Fin n → Nat) (tag : Nat) : Program 3 :=
  let result := typeMember (.composition (OriginalHeadResult.branchResult tag) (fun _ : Fin 1 => .projection 0))
  if tag = 4 then InternalAcceptance.conjunction result applicationArguments
  else if tag = 5 then InternalAcceptance.conjunction
    (.composition contains ![.projection 1,.projection 0])
    (InternalAcceptance.conjunction result (rankedArguments n arity))
  else result
/-- Raw-head inputs [head,symbol-list,type-list]. The payload branch uses the same lists. -/
def atPayload (n : Nat) (arity : Fin n → Nat) (tag : Nat) : Program 3 :=
  .composition (branchWindow n arity tag) ![InternalApplicationCertificateConstructors.rightOf (.projection 0),.projection 1,.projection 2]
def choose (tag : Nat) (yes no : Program 3) : Program 3 :=
  InternalAcceptance.branch (sameOf (InternalApplicationCertificateConstructors.leftOf (.projection 0)) (constant 3 tag)) no yes
def window (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  choose 0 (atPayload n arity 0) (choose 1 (atPayload n arity 1)
    (choose 2 (atPayload n arity 2) (choose 3 (atPayload n arity 3)
      (choose 4 (atPayload n arity 4) (choose 5 (atPayload n arity 5) (constant 3 0))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow
