module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryCombinedStep
open OriginalHereditaryVisitScheduler (visitNumber returnNumber)
def VisitDispatch : Prop := ∀ (R : Program 2) (j tail result : Nat),
  let state := Nat.pair (1+Nat.pair (visitNumber j) tail) result
  evaluate (step R) (List.Vector.ofFn ![state]) =
    evaluate OriginalHereditaryAnnotatedVisit.step (List.Vector.ofFn ![state])
def ReturnDispatch : Prop := ∀ (R : Program 2) (j a d tail result : Nat),
  let state := Nat.pair (1+Nat.pair (returnNumber j a d) tail) result
  evaluate (step R) (List.Vector.ofFn ![state]) =
    evaluate (OriginalHereditaryReturnStep.step R) (List.Vector.ofFn ![state])
/-- Unknown tags and empty work are identity. A supported but malformed return
inherits the exact checked return Program behavior, not a fictitious pop law. -/
def UnsupportedIdentity : Prop :=
  (∀ (R : Program 2) (result : Nat), evaluate (step R) (List.Vector.ofFn ![Nat.pair 0 result]) = Nat.pair 0 result) ∧
  (∀ (R : Program 2) (f tail result : Nat), (Nat.unpair f).1 ≠ 0 → (Nat.unpair f).1 ≠ 1 →
    evaluate (step R) (List.Vector.ofFn ![Nat.pair (1+Nat.pair f tail) result]) =
      Nat.pair (1+Nat.pair f tail) result)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepTargets
