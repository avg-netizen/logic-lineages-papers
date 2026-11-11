module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidity
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open OriginalHereditaryValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Evaluation of a literal binary AST at the original raw value/parameter.
This is native evaluation, not an internal graph or a reflection principle. -/
def binaryValue (p : Program 2) (value parameter : Nat) : Nat :=
  evaluate p (List.Vector.ofFn ![value,parameter])

/-- A literal lambda payload is compatible with its outer type exactly when
that type is the successor/pair arrow of the ACTUAL payload domain and the
outer arrow's codomain. In particular outer type zero and domain mismatch
must reject. A lambda tag alone does not establish this shape. -/
def lambdaShapeValue (value : Nat) : Nat :=
  if resultTypeValue value =
    Nat.succ (Nat.pair (domainValue value) (lambdaCodomainValue value)) then 1 else 0

/-- Transparent source-root callback. Applications defer to their children
and the validator's original result-membership check. Lambdas pay BOTH the
outer-arrow and domain memberships here; the child's source test pays the
codomain membership. All other tags retain the WHOLE original source leaf.
Arbitrary non-one membership outputs reject. -/
def sourceRootValue (oldSource member : Nat → Nat → Nat)
    (value parameter : Nat) : Nat :=
  if tagValue value = 2 then 1
  else if tagValue value = 1 then
    if lambdaShapeValue value = 1 ∧
      member (resultTypeValue value) parameter = 1 ∧
      member (domainValue value) parameter = 1 then 1 else 0
  else oldSource value parameter

/-- Target validity has NO universe membership filter, including at
applications. Lambda roots check only their original arrow/domain shape;
their actual typed body is visited by the unchanged bounded validator. -/
def targetRootValue (oldTarget : Nat → Nat → Nat)
    (value parameter : Nat) : Nat :=
  if tagValue value = 2 then 1
  else if tagValue value = 1 then lambdaShapeValue value
  else oldTarget value parameter

/-- All selectors below are total binary ASTs with inputs [value,parameter].
The codomain is a raw type NUMBER, not an Encodable Gamma code. -/
def resultType : Program 2 := leftOf (.projection 0)

def tag : Program 2 :=
  .composition OriginalLambdaConstructor.tag (fun _ : Fin 1 => .projection 0)

def domain : Program 2 :=
  .composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => .projection 0)

def codomain : Program 2 :=
  .composition InternalListCodec.tailCode (fun _ : Fin 1 => resultType)

def lambdaShape : Program 2 :=
  InternalApplicationStepPeel.same resultType (consOf domain codomain)

/-- This callback contains no recursive source or validity oracle. Only the
nonapplication/nonlambda branch calls data.oldSource. Its lambda tests use
the SAME parameter and the ACTUAL outer type and payload domain. -/
def sourceRoot (data : Data) : Program 2 :=
  InternalAcceptance.branch (InternalApplicationStepPeel.same tag (two 2))
    (InternalAcceptance.branch
      (InternalApplicationStepPeel.same tag (InternalLessThan.constantOne 2))
      data.oldSource
      (InternalAcceptance.conjunction lambdaShape
        (InternalAcceptance.conjunction
          (exactOne (.composition data.member ![resultType,.projection 1]))
          (exactOne (.composition data.member ![domain,.projection 1])))))
    (InternalLessThan.constantOne 2)

def targetRoot (data : Data) : Program 2 :=
  InternalAcceptance.branch (InternalApplicationStepPeel.same tag (two 2))
    (InternalAcceptance.branch
      (InternalApplicationStepPeel.same tag (InternalLessThan.constantOne 2))
      data.oldTarget lambdaShape)
    (InternalLessThan.constantOne 2)

/-- HS reuses the EXISTING arbitrary-callback validator, its payload+1 fuel,
its actual application children, and its extended-Gamma lambda body. N is
exactly normalizeData (BottomParameter.baseData rawData), not the later final
selected tuple. No oldSource test hides the lambda body behind a root oracle. -/
def sourceValidator (rawData : Data) : Program 2 :=
  let N := normalizedData rawData
  validator (sourceRoot N) (targetRoot N) N.member

/-- HT uses constant one for BOTH the second root callback and the member
callback. Supplying N.member here would incorrectly reject original target
applications outside the finite source window. -/
def targetValidator (rawData : Data) : Program 2 :=
  let N := normalizedData rawData
  validator (targetRoot N) (InternalLessThan.constantOne 2)
    (InternalLessThan.constantOne 2)

def sourceValidatorValue (rawData : Data) (value parameter : Nat) : Nat :=
  let N := normalizedData rawData
  validatorValue
    (sourceRootValue (binaryValue N.oldSource) (binaryValue N.member))
    (targetRootValue (binaryValue N.oldTarget))
    (binaryValue N.member) value parameter

def targetValidatorValue (rawData : Data) (value parameter : Nat) : Nat :=
  let N := normalizedData rawData
  validatorValue (targetRootValue (binaryValue N.oldTarget))
    (fun _ _ => 1) (fun _ _ => 1) value parameter

/-- Replace BOTH raw validity leaves by the concrete transparent validators.
The original raw representative and membership ASTs are retained literally.
All-input equality and full four-leaf calibration are obligations, not fields. -/
def refineData (rawData : Data) : Data :=
  { rawData with
    oldSource := sourceValidator rawData
    oldTarget := targetValidator rawData }

/- NATIVE TRANSPARENT-VALIDITY PACKET ONLY. The separate future contracts for
internal recurrence of these exact ASTs, reconstruction of lambda source
acceptance at the SAME eventual final source Program, canonical-body coherence,
and transport retaining the entire global Package remain PENDING. Native
evaluation equality is not an internal graph implication. None of those
future obligations may be replaced by an opaque root-source premise. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidity
