module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceTargets
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrence
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact native recurrence of the EXISTING payload+1 bounded machine on ALL
raw values and parameters, for arbitrary possibly non-Boolean leaves. Both
application children and the extended-Gamma lambda body invoke the SAME
validator, each with its OWN payload+1 fuel. Nonapplication/nonlambda values
require only nodeCheck. No termination, successful run, recurrence or typed
source premise is supplied. The Boolean conjunct includes every rejection. -/
def ActualOriginalHereditaryValidatorRecurrence : Prop :=
  ∀ (oldSource oldTarget member : Nat → Nat → Nat) (value parameter : Nat),
  (validatorValue oldSource oldTarget member value parameter = 0 ∨
    validatorValue oldSource oldTarget member value parameter = 1) ∧
  (validatorValue oldSource oldTarget member value parameter = 1 ↔
    nodeCheckValue oldSource oldTarget member value parameter = 1 ∧
      (if tagValue value = 2 then
        validatorValue oldSource oldTarget member
            (functionChildValue value) parameter = 1 ∧
          validatorValue oldSource oldTarget member
            (argumentChildValue value) parameter = 1
      else if tagValue value = 1 then
        validatorValue oldSource oldTarget member
          (lambdaBodyValue value) (childParameterValue value parameter) = 1
      else True))

/-- The same recurrence for the ACTUAL Program AST, not a replacement tree
predicate. nodeCheck is evaluated on the literal singleton initial state.
All child calls are the identical validator AST with their exact raw inputs
and parameter, including malformed inputs and non-one leaf outputs. -/
def ActualOriginalHereditaryProgramRecurrence : Prop :=
  ∀ (oldSource oldTarget member : Program 2) (value parameter : Nat),
  (evaluate (validator oldSource oldTarget member)
      (List.Vector.ofFn ![value,parameter]) = 1 ↔
    evaluate (nodeCheck oldSource oldTarget member)
        (List.Vector.ofFn ![initialValue value parameter]) = 1 ∧
      (if tagValue value = 2 then
        evaluate (validator oldSource oldTarget member)
            (List.Vector.ofFn ![functionChildValue value,parameter]) = 1 ∧
          evaluate (validator oldSource oldTarget member)
            (List.Vector.ofFn ![argumentChildValue value,parameter]) = 1
      else if tagValue value = 1 then
        evaluate (validator oldSource oldTarget member)
          (List.Vector.ofFn ![lambdaBodyValue value,
            childParameterValue value parameter]) = 1
      else True))

/-- Original source acceptance supplies the typed-window invariant at EVERY
application/lambda descendant frame. Lambda descendants retain literal
context and actual cons-encoded Gamma through childParameterValue, never the
numbering of a substituted context. No subtype-closed S, window-validity or
child-source-acceptance premise is allowed. This is a native semantic fact,
not an internal graph rule. -/
def ActualOriginalHereditarySourceDescendantInvariant : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (value parameter : Nat),
  InternalOriginalUniformParameterLeaves.sourceValue n arity
    (List.Vector.ofFn ![value,parameter]) = 1 →
  ∀ frame : Frame, DescendantFrame ⟨value,parameter⟩ frame →
    TypedWindowFrame n arity (Nat.unpair parameter).1 frame

/-- Full-output redundancy of the concrete guard on EVERY original raw
input under only the ORIGINAL all-input four-leaf calibration. Its captured
leaves are precisely N.oldSource, N.oldTarget and N.member for
N = normalizeData (BottomParameter.baseData rawData). This includes rejected
values, malformed contexts and every raw Gamma/parameter; no hS closure,
hereditary-validity or recursive acceptance assumption is supplied. -/
def ActualOriginalHereditarySourceGuardRedundancy : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (rawData : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity rawData →
    ∀ v : List.Vector Nat 2,
      evaluate (guard rawData) v = evaluate rawData.oldSource v

/-- The refinement changes the RAW oldSource to its literal conjunction with
the concrete guard. Equality is all-input/full-output, and the complete
original four-leaf calibration is retained with no changed source semantics.
No final selected tuple, internal closure law or Package retention is claimed. -/
def ActualOriginalHereditarySourceRefinementCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (rawData : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity rawData →
    (∀ v : List.Vector Nat 2,
      evaluate (refineData rawData).oldSource v = evaluate rawData.oldSource v) ∧
    InternalOriginalUniformDescentSelection.Calibrated n arity (refineData rawData)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceTargets
