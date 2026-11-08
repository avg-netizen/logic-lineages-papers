module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationTargets
open InternalApplicationResultStack InternalParameterizedApplicationResultStack
open InternalParameterizedApplicationResultFoldCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The independently defined original payload fold opens exactly tag two
with G(original whole packed value,p)=1. Both recursive children retain the
SAME p, and C receives function before argument. Every other raw root falls
back to L on that whole original root. No validity or output premise occurs. -/
def ActualOriginalParameterizedSemanticResultFoldEquation : Prop :=
  ∀ (guard leaf : Program 2) (combine : Program 5) (value parameter : Nat),
  semanticFoldP guard leaf combine value parameter =
    if InternalApplicationValidityStack.tagValue value = 2 ∧
        evaluate guard (List.Vector.ofFn ![value,parameter]) = 1 then
      evaluate combine (List.Vector.ofFn
        ![InternalApplicationValidityStack.domainValue value,
          InternalApplicationValidityStack.resultTypeValue value,
          semanticFoldP guard leaf combine
            (InternalApplicationValidityStack.functionChildValue value) parameter,
          semanticFoldP guard leaf combine
            (InternalApplicationValidityStack.argumentChildValue value) parameter,
          parameter])
    else evaluate leaf (List.Vector.ofFn ![value,parameter])

/-- Every count, including zero, and every original structured state:
non-one status, malformed frame tags, finish underflow and arbitrary whole
results are retained. The actual parameterized AST returns the complete
original encoded state, not its outer carry pair, a status bit or a head.
The right side is the existing structured execution with callbacks sliced
at p. Its semantics and work measure are not redefined in this packet. -/
def ActualOriginalParameterizedEncodedResultStackIteration : Prop :=
  ∀ (guard leaf : Program 2) (combine : Program 5)
    (count : Nat) (state : State) (parameter : Nat),
  evaluate (iterateP guard leaf combine)
      (List.Vector.ofFn ![count, encodeState state, parameter]) =
    encodeState (InternalApplicationResultFoldCalibration.stateIterate
      (fun x => evaluate guard (List.Vector.ofFn ![x,parameter]))
      (fun x => evaluate leaf (List.Vector.ofFn ![x,parameter]))
      (fun d e f a => evaluate combine (List.Vector.ofFn ![d,e,f,a,parameter])) count state)

/-- On ALL raw original inputs and every p, the existing runP at its exact
original fuel returns status one, empty work and the singleton independent
semantic result. The existing foldP returns that same arbitrary Nat result,
including zero. Neither the parameter, the carried pair, the packed type nor
computed output sizes change fuel. No successful-run, callback-correctness,
source-validity, representative or internal-derivability premise occurs. -/
def ActualOriginalParameterizedBoundedResultFoldCalibration : Prop :=
  ∀ (guard leaf : Program 2) (combine : Program 5) (value parameter : Nat),
  let result := semanticFoldP guard leaf combine value parameter
  evaluate (runP guard leaf combine) (List.Vector.ofFn ![value,parameter]) =
      encodeState (⟨1, [], [result]⟩ : State) ∧
    evaluate (foldP guard leaf combine) (List.Vector.ofFn ![value,parameter]) = result

/-- Separate external calibration of the ACTUAL whole-state check on every
raw input and parameter. Its accepted singleton may contain zero. This is
not an internal graph derivation of goodRunP=1 and cannot be used as semantic
truth-to-derivability reflection or a canonical-leaf selection theorem. -/
def ActualOriginalParameterizedResultFoldGoodRunCalibration : Prop :=
  ∀ (guard leaf : Program 2) (combine : Program 5) (value parameter : Nat),
  evaluate (goodRunP guard leaf combine) (List.Vector.ofFn ![value,parameter]) = 1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationTargets
