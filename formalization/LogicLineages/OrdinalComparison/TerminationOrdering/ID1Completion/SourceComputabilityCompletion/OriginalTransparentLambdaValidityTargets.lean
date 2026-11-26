module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityTargets
open OriginalHereditaryValidity
open OriginalTransparentLambdaValidity
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full-output application recurrence for the ACTUAL original source and
target on ALL raw values and parameters. The target equation has NO membership
condition. A raw Gamma is decoded through the original total Object codec;
the original outer context decoder still rejects every malformed context.
No decoded-context, subtype-closure, valid-window or Gamma-membership premise
is supplied. This is a native semantic equation, not an internal graph law. -/
def ActualOriginalTransparentApplicationEquations : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (value parameter : Nat),
  tagValue value = 2 →
  let S := fun x p => InternalOriginalUniformParameterLeaves.sourceValue n arity
    (List.Vector.ofFn ![x,p])
  let T := fun x p => InternalOriginalUniformParameterLeaves.targetValue n arity
    (List.Vector.ofFn ![x,p])
  let M := fun x p => InternalOriginalUniformParameterLeaves.memberValue n
    (List.Vector.ofFn ![x,p])
  (T value parameter =
    if T (functionChildValue value) parameter = 1 ∧
      T (argumentChildValue value) parameter = 1 then 1 else 0) ∧
  (S value parameter =
    if M (resultTypeValue value) parameter = 1 ∧
      S (functionChildValue value) parameter = 1 ∧
      S (argumentChildValue value) parameter = 1 then 1 else 0)

/-- Full-output lambda recurrence for the ACTUAL original leaves on ALL raw
inputs. Shape is the literal equality t = succ(pair d e); b is the original
body repacked at e and p' retains the outer context while consing d onto the
original encoded Gamma. Source checks BOTH t and d membership. Codomain
membership follows from the actual child's source test, not window closure.
Malformed outer contexts must still reject through the original leaves.
Neither a successful decoder nor any child-acceptance premise is assumed. -/
def ActualOriginalTransparentLambdaEquations : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (value parameter : Nat),
  tagValue value = 1 →
  let S := fun x p => InternalOriginalUniformParameterLeaves.sourceValue n arity
    (List.Vector.ofFn ![x,p])
  let T := fun x p => InternalOriginalUniformParameterLeaves.targetValue n arity
    (List.Vector.ofFn ![x,p])
  let M := fun x p => InternalOriginalUniformParameterLeaves.memberValue n
    (List.Vector.ofFn ![x,p])
  (T value parameter =
    if lambdaShapeValue value = 1 ∧
      T (lambdaBodyValue value) (childParameterValue value parameter) = 1
      then 1 else 0) ∧
  (S value parameter =
    if lambdaShapeValue value = 1 ∧
      M (resultTypeValue value) parameter = 1 ∧
      M (domainValue value) parameter = 1 ∧
      S (lambdaBodyValue value) (childParameterValue value parameter) = 1
      then 1 else 0)

/-- Literal raw/AST equations for every selector and BOTH root callbacks.
The Data tuple is arbitrary and its callbacks may return non-Boolean values.
No original calibration, typing or membership assumption is available. -/
def ActualOriginalTransparentRootCalibration : Prop :=
  (∀ v : List.Vector Nat 2,
    evaluate resultType v = resultTypeValue (v.get 0) ∧
    evaluate tag v = tagValue (v.get 0) ∧
    evaluate domain v = domainValue (v.get 0) ∧
    evaluate codomain v = lambdaCodomainValue (v.get 0) ∧
    evaluate lambdaShape v = lambdaShapeValue (v.get 0)) ∧
  (∀ (data : Data) (v : List.Vector Nat 2),
    evaluate (sourceRoot data) v =
      sourceRootValue (binaryValue data.oldSource) (binaryValue data.member)
        (v.get 0) (v.get 1) ∧
    evaluate (targetRoot data) v =
      targetRootValue (binaryValue data.oldTarget) (v.get 0) (v.get 1))

/-- Calibrate the actual bounded HS/HT Programs to their concrete numeric
machines on EVERY raw input, for arbitrary rawData. The original payload+1
fuel and independently changing per-frame parameter are unchanged. -/
def ActualOriginalTransparentValidatorCalibration : Prop :=
  ∀ (rawData : Data) (v : List.Vector Nat 2),
    evaluate (sourceValidator rawData) v =
      sourceValidatorValue rawData (v.get 0) (v.get 1) ∧
    evaluate (targetValidator rawData) v =
      targetValidatorValue rawData (v.get 0) (v.get 1)

/-- HS equals the ACTUAL original source leaf on ALL inputs and all outputs,
under only original four-leaf calibration. Rejected and malformed inputs are
included. In particular this is not conditional on typed-window descendants,
accepted root source, subtype closure or a supplied recurrence hypothesis. -/
def ActualOriginalTransparentSourceEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (rawData : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity rawData →
  ∀ v : List.Vector Nat 2,
    evaluate (sourceValidator rawData) v = evaluate rawData.oldSource v

/-- HT equals the ACTUAL original target leaf on ALL inputs and all outputs,
including valid terms outside the source window and malformed outer contexts.
There is no universe-membership or source-acceptance hypothesis. -/
def ActualOriginalTransparentTargetEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (rawData : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity rawData →
  ∀ v : List.Vector Nat 2,
    evaluate (targetValidator rawData) v = evaluate rawData.oldTarget v

/-- BOTH replaced leaves are all-input/full-output equal to their original
leaves, BOTH untouched AST fields are literally retained, and the COMPLETE
original four-field calibration survives. This does not assert internal
lambda reconstruction, canonical-body coherence or final Package transport. -/
def ActualOriginalTransparentRefinementCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (rawData : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity rawData →
  (OriginalTransparentLambdaValidity.refineData rawData).oldRepresentative =
      rawData.oldRepresentative ∧
  (OriginalTransparentLambdaValidity.refineData rawData).member = rawData.member ∧
  (∀ v : List.Vector Nat 2,
    evaluate (OriginalTransparentLambdaValidity.refineData rawData).oldSource v =
        evaluate rawData.oldSource v ∧
    evaluate (OriginalTransparentLambdaValidity.refineData rawData).oldTarget v =
        evaluate rawData.oldTarget v ∧
    evaluate (OriginalTransparentLambdaValidity.refineData rawData).oldRepresentative v =
        evaluate rawData.oldRepresentative v ∧
    evaluate (OriginalTransparentLambdaValidity.refineData rawData).member v =
        evaluate rawData.member v) ∧
  InternalOriginalUniformDescentSelection.Calibrated n arity
    (OriginalTransparentLambdaValidity.refineData rawData)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityTargets
