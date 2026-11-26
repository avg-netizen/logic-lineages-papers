module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountOpenConsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalControlGraphSupportProof (equalEqn projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (unaryValue binaryValue)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchIntro)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant sameOf succOf)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (consValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralCount (entryCount entryStep)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeTwo (c n : OTerm α) :
    (![c,n] : Fin 2 → OTerm α) = Fin.cons c (![n] : Fin 1 → OTerm α) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

private theorem tapeThree (c h n : OTerm α) :
    (![c,h,n] : Fin 3 → OTerm α) = Fin.cons c (Fin.cons h (![n] : Fin 1 → OTerm α)) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

private theorem eraseHeadCounts (code head tail needle acc out : OTerm α)
    (hc : Nonempty (Derivation B Γ (consGraph code head tail)))
    (hr : Nonempty (Derivation B Γ (counted tail needle acc)))
    (hs : Nonempty (Derivation B Γ (programGraph entryStep out ![head,acc,needle]))) :
    Nonempty (Derivation B Γ (counted code needle out)) := by
  have prior : Nonempty (Derivation B Γ (recGraph (constant 1 0) entryStep acc tail ![needle])) := by
    simpa only [counted,tapeTwo,recGraph,entryCount] using hr
  have step : Nonempty (Derivation B Γ
      (programGraph entryStep out (Fin.cons head (Fin.cons acc ![needle])))) := by
    rw [← tapeThree]
    exact hs
  have result := consValue (constant 1 0) entryStep code head tail acc out ![needle] hc prior step
  simpa only [counted,tapeTwo,recGraph,entryCount] using result

/-- Deleting the chosen head decreases its literal multiplicity by one:
the original tape count is the successor of the count on the residual tape. -/
theorem chosenHead (code head tail needle acc : OTerm α)
    (hc : Nonempty (Derivation B Γ (consGraph code head tail)))
    (hr : Nonempty (Derivation B Γ (counted tail needle acc)))
    (he : Nonempty (Derivation B Γ (eqn head needle))) :
    Nonempty (Derivation B Γ (counted code needle (suc acc))) := by
  let xs : Fin 3 → OTerm α := ![head,acc,needle]
  let q : Program 3 := sameOf (.projection 0) (.projection 2)
  have hit : Nonempty (Derivation B Γ (programGraph q (suc z) xs)) :=
    binaryValue equalityTest (.projection 0) (.projection 2) (suc z) head needle xs
      (equalityOfEqual head needle he) (projectionValue 0 xs) (projectionValue 2 xs)
  have next : Nonempty (Derivation B Γ (programGraph (succOf (.projection 1)) (suc acc) xs)) :=
    unaryValue .succ (.projection 1) (suc acc) acc xs
      (successorValue (Fin.cons acc Fin.elim0)) (projectionValue 1 xs)
  exact eraseHeadCounts code head tail needle acc (suc acc) hc hr
    (successorBranchIntro q (.projection 1) (succOf (.projection 1)) (suc acc) z xs hit next)

/-- Deleting the same head leaves each unequal query's literal count unchanged. -/
theorem otherHead (code head tail needle acc : OTerm α)
    (hc : Nonempty (Derivation B Γ (consGraph code head tail)))
    (hr : Nonempty (Derivation B Γ (counted tail needle acc)))
    (he : Nonempty (Derivation B Γ (eqn head needle).not)) :
    Nonempty (Derivation B Γ (counted code needle acc)) := by
  let xs : Fin 3 → OTerm α := ![head,acc,needle]
  let q : Program 3 := sameOf (.projection 0) (.projection 2)
  have neq : Nonempty (Derivation B Γ (equal head needle).not) := by
    simpa only [equalEqn] using he
  have miss : Nonempty (Derivation B Γ (programGraph q z xs)) :=
    sameReject (.projection 0) (.projection 2) head needle xs
      (projectionValue 0 xs) (projectionValue 2 xs) neq
  exact eraseHeadCounts code head tail needle acc acc hc hr
    (zeroBranchIntro q (.projection 1) (succOf (.projection 1)) acc xs miss (projectionValue 1 xs))

#print axioms chosenHead
#print axioms otherHead
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountOpenConsProof
