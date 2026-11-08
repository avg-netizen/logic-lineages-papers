module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeel
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The leaf keeps the ORIGINAL source-universe, target-packed and
argument-universe decoders. Inputs are [domain,codomain,function,target,argument].
The target is deliberately not required to belong to the universe. -/
def endpointValue (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (v : List.Vector Nat 5) : Nat :=
  match NumberedNumericDecoding.decodeType (v.get 0),
      NumberedNumericDecoding.decodeType (v.get 1),
      NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma (v.get 2),
      NumberedNumericDecoding.decodePackedNumber n arity Gamma (v.get 3),
      NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma (v.get 4) with
  | some sigma, some tau, some q, some r, some a =>
      (decide (q.1 = .arrow sigma tau ∧ r.1 = .arrow sigma tau ∧
        a.1 = sigma ∧ tau ∈ S)).toNat
  | _, _, _, _, _ => 0

/-- All natural inputs are calibrated, including malformed packed terms and
rejected windows. This semantic condition supplies no internal derivation. -/
def EndpointCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (endpoint : Program 5) : Prop :=
  ∀ v : List.Vector Nat 5, evaluate endpoint v = endpointValue n arity symbols S Gamma v

/-- Every selector is built from the already calibrated ORIGINAL pair inverses. -/
def outerType (p : Program 1) : Program 1 := leftOf p
def constructorTag (p : Program 1) : Program 1 := leftOf (rightOf p)
def appBody (p : Program 1) : Program 1 := rightOf (rightOf p)
def appDomain (p : Program 1) : Program 1 := leftOf (appBody p)
def functionPayload (p : Program 1) : Program 1 := leftOf (rightOf (appBody p))
def argumentPayload (p : Program 1) : Program 1 := rightOf (rightOf (appBody p))

def rawPath : Program 1 := leftOf step
def pathHead : Program 1 := .composition InternalListCodec.headCode (fun _ : Fin 1 => rawPath)
def pathTail : Program 1 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => rawPath)

def domain : Program 1 := appDomain source
def codomain : Program 1 := outerType source
/-- The original arrow-type code is the same successor-of-pair arithmetic AST. -/
def arrowType : Program 1 := consOf domain codomain

def functionCode : Program 1 := pairOf arrowType (functionPayload source)
def targetFunctionCode : Program 1 := pairOf arrowType (functionPayload target)
def argumentCode : Program 1 := pairOf domain (argumentPayload source)
def peeledStep : Program 1 := pairOf pathTail (rightOf step)
def peeledState : Program 1 :=
  .composition edgeCode ![functionCode,targetFunctionCode,peeledStep]

def same {n : Nat} (p q : Program n) : Program n :=
  .composition InternalEqualityTest.equalityTest ![p,q]

def nonemptyPath : Program 1 :=
  InternalAcceptance.branch rawPath (InternalAcceptance.constantZero 1)
    (InternalLessThan.constantOne 1)

/-- No transition accepts a structural mismatch. In particular, the two outer
result tags, domain tags and complete argument payloads must agree. -/
def structuralGuard : Program 1 :=
  InternalAcceptance.conjunction nonemptyPath
    (InternalAcceptance.conjunction (same pathHead (two 1))
      (InternalAcceptance.conjunction (same (constructorTag source) (two 1))
        (InternalAcceptance.conjunction (same (constructorTag target) (two 1))
          (InternalAcceptance.conjunction (same (outerType source) (outerType target))
            (InternalAcceptance.conjunction (same (appDomain source) (appDomain target))
              (same (argumentPayload source) (argumentPayload target)))))))

/-- Explicit numeric outer-type checks are not hidden inside the decoder
leaf. The two functions have the original arrow tag; the argument has the
domain tag. These checks are redundant only after reconstruction has been proved. -/
def endpointTypeGuard : Program 5 :=
  InternalAcceptance.conjunction
    (same (leftOf (.projection 2)) (consOf (.projection 0) (.projection 1)))
    (InternalAcceptance.conjunction
      (same (leftOf (.projection 3)) (consOf (.projection 0) (.projection 1)))
      (same (leftOf (.projection 4)) (.projection 0)))

def endpointGuard (endpoint : Program 5) : Program 5 :=
  InternalAcceptance.conjunction endpointTypeGuard endpoint

def endpointAt (endpoint : Program 5) : Program 1 :=
  .composition (endpointGuard endpoint)
    ![domain,codomain,functionCode,targetFunctionCode,argumentCode]

def guard (endpoint : Program 5) : Program 1 :=
  InternalAcceptance.conjunction structuralGuard (endpointAt endpoint)

/-- The one-step transition is an explicit unary original PR AST on the
original edgeCode state. Every failed guard returns the input state unchanged. -/
def transition (endpoint : Program 5) : Program 1 :=
  InternalAcceptance.branch (guard endpoint) (.projection 0) peeledState

/-- Iteration is over the ORIGINAL raw certificate path, without rank or fuel.
The raw-list recursor ignores head values; the transition checks the current
certificate head itself. These definitions do not assert checker correctness. -/
def normalizer (endpoint : Program 5) : Program 1 :=
  .composition (InternalRawListRepeat.repeatProgram (transition endpoint))
    ![rawPath,.projection 0]

def checkedState (endpoint : Program 5) (oldChecker : Program 3) : Program 1 :=
  .composition (.composition oldChecker ![source,target,step])
    (fun _ : Fin 1 => normalizer endpoint)

/-- Inputs stay [source,target,certificate]. The old checker is applied to
all three original selectors of the fully repeated state, at its full output. -/
def checker (endpoint : Program 5) (oldChecker : Program 3) : Program 3 :=
  .composition (checkedState endpoint oldChecker) (fun _ : Fin 1 => edgeCode)

/-- A direct numeric view of the ORIGINAL state fields, independent of Program
execution. Defaults arise only from the original total numeric selectors. -/
structure View where
  source : Nat
  target : Nat
  certificate : Nat
  path : Nat
  pathHead : Nat
  pathTail : Nat
  payload : Nat
  sourceType : Nat
  targetType : Nat
  sourceTag : Nat
  targetTag : Nat
  domain : Nat
  targetDomain : Nat
  functionPayload : Nat
  targetFunctionPayload : Nat
  argumentPayload : Nat
  targetArgumentPayload : Nat

def view (state : Nat) : View :=
  let s := (Nat.unpair state).1
  let t := (Nat.unpair (Nat.unpair state).2).1
  let k := (Nat.unpair (Nat.unpair state).2).2
  let path := (Nat.unpair k).1
  let sb := (Nat.unpair (Nat.unpair s).2).2
  let tb := (Nat.unpair (Nat.unpair t).2).2
  { source := s, target := t, certificate := k, path := path,
    pathHead := (Nat.unpair (path - 1)).1, pathTail := (Nat.unpair (path - 1)).2,
    payload := (Nat.unpair k).2,
    sourceType := (Nat.unpair s).1, targetType := (Nat.unpair t).1,
    sourceTag := (Nat.unpair (Nat.unpair s).2).1,
    targetTag := (Nat.unpair (Nat.unpair t).2).1,
    domain := (Nat.unpair sb).1, targetDomain := (Nat.unpair tb).1,
    functionPayload := (Nat.unpair (Nat.unpair sb).2).1,
    targetFunctionPayload := (Nat.unpair (Nat.unpair tb).2).1,
    argumentPayload := (Nat.unpair (Nat.unpair sb).2).2,
    targetArgumentPayload := (Nat.unpair (Nat.unpair tb).2).2 }

def endpointInputs (v : View) : List.Vector Nat 5 :=
  let arrow := 1 + Nat.pair v.domain v.sourceType
  List.Vector.ofFn ![v.domain,v.sourceType,Nat.pair arrow v.functionPayload,
    Nat.pair arrow v.targetFunctionPayload,Nat.pair v.domain v.argumentPayload]

def shape (v : View) : Bool :=
  decide (v.path ≠ 0 ∧ v.pathHead = 2 ∧ v.sourceTag = 2 ∧ v.targetTag = 2 ∧
    v.sourceType = v.targetType ∧ v.domain = v.targetDomain ∧
    v.argumentPayload = v.targetArgumentPayload)

def guardValue (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (state : Nat) : Nat :=
  let v := view state
  if shape v && decide (endpointValue n arity symbols S Gamma (endpointInputs v) = 1)
    then 1 else 0

def peeledValue (state : Nat) : Nat :=
  let v := view state
  let inputs := endpointInputs v
  Nat.pair (inputs.get 2) (Nat.pair (inputs.get 3) (Nat.pair v.pathTail v.payload))

def transitionValue (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (state : Nat) : Nat :=
  if guardValue n arity symbols S Gamma state = 1 then peeledValue state else state

abbrev graph5 {α : Type} (p : Program 5) (out d e s t a : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph p out (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a Fin.elim0)))))

/-- Outer tags are indispensable: rawApplication discards them. No successful
semantic decoding is silently converted into these original graph premises. -/
def taggedEdge {α : Type} (d e arrow s t a certificate k : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (graph1 InternalUnpair.left arrow s ⊓
      (graph1 InternalUnpair.left arrow t ⊓
        (graph1 InternalUnpair.left d a ⊓ graph3 edgeCode certificate s t k)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeel
