module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTargets
open OriginalLambdaTraversal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- EVERY raw state and arbitrary binary leaf, including malformed frames,
non-one statuses, arbitrary parameters and every result-stack underflow. -/
def ActualOriginalLambdaTraversalTransitionCalibration : Prop :=
  ∀ (leaf : Program 2) (state : Nat),
  evaluate (transition leaf) (List.Vector.ofFn ![state]) =
    transitionValue (fun value parameter =>
      evaluate leaf (List.Vector.ofFn ![value,parameter])) state

/-- The original pair/list codecs identify structured and direct execution.
Numeric frames are unrestricted; this is not merely a reachable-state law. -/
def ActualOriginalLambdaTraversalEncodedTransition : Prop :=
  ∀ (leaf : Nat → Nat → Nat) (state : State),
  transitionValue leaf (encodeState state) = encodeState (stateStep leaf state)

/-- Exact selector/constructor calibration on ALL inputs. In particular the
lambda codomain uses truncated predecessor at outer type zero, the body has
that actual codomain, and the child parameter uses actual encoded Gamma. -/
def ActualOriginalLambdaTraversalSelectorCalibration : Prop :=
  (∀ value : Nat,
    evaluate rawType (List.Vector.ofFn ![value]) = resultTypeValue value ∧
    evaluate rawTag (List.Vector.ofFn ![value]) = tagValue value ∧
    evaluate rawDomain (List.Vector.ofFn ![value]) = domainValue value ∧
    evaluate rawFunction (List.Vector.ofFn ![value]) = functionChildValue value ∧
    evaluate rawArgument (List.Vector.ofFn ![value]) = argumentChildValue value ∧
    evaluate rawCodomain (List.Vector.ofFn ![value]) = lambdaCodomainValue value ∧
    evaluate rawBody (List.Vector.ofFn ![value]) = lambdaBodyValue value) ∧
  (∀ value parameter : Nat,
    evaluate childParameter (List.Vector.ofFn ![value,parameter]) =
      childParameterValue value parameter) ∧
  (∀ d e f a : Nat,
    evaluate InternalApplicationCertificateConstructors.application
      (List.Vector.ofFn ![d,e,f,a]) = applicationValue d e f a) ∧
  (∀ d e b : Nat,
    evaluate OriginalLambdaConstructor.constructor (List.Vector.ofFn ![d,e,b]) =
      lambdaValue d e b)

/-- The exact budget is twice the ORIGINAL term payload plus one. Both
return steps are paid. No bound on context codes, typed children or outputs
is substituted for a payload bound. These inequalities include raw nodes. -/
def ActualOriginalLambdaTraversalFuelBounds : Prop :=
  (∀ value parameter : Nat,
    evaluate fuel (List.Vector.ofFn ![value,parameter]) = fuelValue value ∧
    workWeight [visitValue value parameter] = fuelValue value) ∧
  (∀ value : Nat, tagValue value = 2 →
    1 + fuelValue (functionChildValue value) + fuelValue (argumentChildValue value) + 1 ≤
      fuelValue value) ∧
  (∀ value : Nat, tagValue value = 1 →
    1 + fuelValue (lambdaBodyValue value) + 1 ≤ fuelValue value)

/-- Every nonempty live state decreases, including visits at malformed raw
values and failure at malformed return frames or short result stacks. -/
def ActualOriginalLambdaTraversalWorkDecrease : Prop :=
  ∀ (leaf : Nat → Nat → Nat) (state : State),
  state.status = 1 → state.work ≠ [] →
    workWeight (stateStep leaf state).work < workWeight state.work

/-- Calibration of the actual bounded AST to the direct machine for every
raw input and arbitrary leaf, not calibration to source semantics. -/
def ActualOriginalLambdaTraversalBoundedCalibration : Prop :=
  ∀ leaf : Program 2,
  let L := fun value parameter => evaluate leaf (List.Vector.ofFn ![value,parameter])
  (∀ count initial : Nat,
    evaluate (iterate leaf) (List.Vector.ofFn ![count,initial]) = iterateValue L count initial) ∧
  (∀ state : Nat, evaluate output (List.Vector.ofFn ![state]) = outputValue state) ∧
  (∀ value parameter : Nat,
    evaluate (run leaf) (List.Vector.ofFn ![value,parameter]) = runValue L value parameter ∧
    evaluate (fold leaf) (List.Vector.ofFn ![value,parameter]) = foldValue L value parameter)

/-- An initialized traversal actually finishes with EXACTLY one result at
every sufficient count, for arbitrary leaf outputs and raw inputs. This is
not inferred from work decrease alone, and is not an internal graph law. -/
def ActualOriginalLambdaTraversalNativeTermination : Prop :=
  ∀ (leaf : Nat → Nat → Nat) (value parameter count : Nat),
  fuelValue value ≤ count →
    ∃ out : Nat, iterateValue leaf count (initialValue value parameter) =
      encodeState ⟨1, [], [out]⟩

/-- Full-output equations for the bounded numeric machine, including raw
malformed tag-one/tag-two inputs. The lambda recursion uses the ACTUAL child
parameter, never its parent's Gamma or a merely calibrated replacement. -/
def ActualOriginalLambdaTraversalNativeRecurrence : Prop :=
  ∀ (leaf : Nat → Nat → Nat) (value parameter : Nat),
  (tagValue value = 2 →
    foldValue leaf value parameter =
      applicationValue (domainValue value) (resultTypeValue value)
        (foldValue leaf (functionChildValue value) parameter)
        (foldValue leaf (argumentChildValue value) parameter)) ∧
  (tagValue value = 1 →
    foldValue leaf value parameter =
      lambdaValue (domainValue value) (lambdaCodomainValue value)
        (foldValue leaf (lambdaBodyValue value) (childParameterValue value parameter))) ∧
  (tagValue value ≠ 2 → tagValue value ≠ 1 →
    foldValue leaf value parameter = leaf value parameter)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTargets
