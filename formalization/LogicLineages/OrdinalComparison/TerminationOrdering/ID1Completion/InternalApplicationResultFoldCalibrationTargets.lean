module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationTargets
open InternalApplicationResultStack InternalApplicationResultFoldCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The all-input equation of the independent payload-recursive semantics.
Only original tag two and an exact-one guard open a root. Every other raw
input falls back to the leaf on that same WHOLE original packed input. -/
def ActualOriginalSemanticResultFoldEquation : Prop :=
  ∀ (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat) (value : Nat),
  semanticFold guard leaf combine value =
    if InternalApplicationValidityStack.tagValue value = 2 ∧ guard value = 1 then
      combine (InternalApplicationValidityStack.domainValue value)
        (InternalApplicationValidityStack.resultTypeValue value)
        (semanticFold guard leaf combine
          (InternalApplicationValidityStack.functionChildValue value))
        (semanticFold guard leaf combine
          (InternalApplicationValidityStack.argumentChildValue value))
    else leaf value

/-- Complete iteration of the actual existing AST on every structured state,
including non-one status, malformed frames and insufficient result stacks.
The entire encoded output state is retained, not merely its status or head. -/
def ActualOriginalEncodedResultStackIteration : Prop :=
  ∀ (guard leaf : Program 1) (combine : Program 4) (count : Nat) (state : State),
  evaluate (iterate guard leaf combine) (List.Vector.ofFn ![count, encodeState state]) =
    encodeState (stateIterate
      (fun value => evaluate guard (List.Vector.ofFn ![value]))
      (fun value => evaluate leaf (List.Vector.ofFn ![value]))
      (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a])) count state)

/-- The EXISTING exact work weight suffices for every live input state. One
extra transition covers every status; terminal states retain their entire
results at every further count. Computed output sizes never enter the bound.
Termination alone does not assert success or a singleton result. -/
def ActualOriginalResultStackSufficientFuel : Prop :=
  ∀ (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (state : State) (count : Nat),
  (state.status = 1 → workWeight state.work ≤ count →
    terminal (stateIterate guard leaf combine count state)) ∧
  (workWeight state.work + 1 ≤ count →
    terminal (stateIterate guard leaf combine count state)) ∧
  (terminal state → stateIterate guard leaf combine count state = state)

/-- Exact semantic preservation, including failed configurations, at one
transition and every finite iteration. The meaning is built from the
independent payload fold, not defined by the run or its output selector. -/
def ActualOriginalResultStackMeaningInvariant : Prop :=
  ∀ (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat),
  (∀ state : State,
    stateMeaning guard leaf combine (stateStep guard leaf combine state) =
      stateMeaning guard leaf combine state) ∧
  (∀ (count : Nat) (state : State),
    stateMeaning guard leaf combine (stateIterate guard leaf combine count state) =
      stateMeaning guard leaf combine state)

/-- Every sufficiently fueled original visit succeeds and pushes exactly its
semantic fold value onto an arbitrary whole background result stack. Work is
empty, status is one, and the suffix is literally preserved. There is NO
work suffix here: terminal padding may start an appended work suffix early. -/
def ActualOriginalCompletedResultFold : Prop :=
  ∀ (guard leaf : Nat → Nat) (combine : Nat → Nat → Nat → Nat → Nat)
    (value : Nat) (results : List Nat) (count : Nat),
  fuelValue value ≤ count →
  stateIterate guard leaf combine count (⟨1, [visitValue value], results⟩ : State) =
    (⟨1, [], semanticFold guard leaf combine value :: results⟩ : State)

/-- The EXISTING bounded run has its exact canonical singleton final state,
and the EXISTING fold AST returns the independent semantic fold on ALL raw
inputs. There are no guard/leaf/combine calibration, validity, output-size or
internal-derivability hypotheses. Representative-specific calibration and
internal recursive constructor closure remain separate pending obligations. -/
def ActualOriginalBoundedResultFoldCalibration : Prop :=
  ∀ (guard leaf : Program 1) (combine : Program 4) (value : Nat),
  let result := semanticFold
    (fun x => evaluate guard (List.Vector.ofFn ![x]))
    (fun x => evaluate leaf (List.Vector.ofFn ![x]))
    (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a])) value
  evaluate (run guard leaf combine) (List.Vector.ofFn ![value]) =
      encodeState (⟨1, [], [result]⟩ : State) ∧
    evaluate (fold guard leaf combine) (List.Vector.ofFn ![value]) = result

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationTargets
