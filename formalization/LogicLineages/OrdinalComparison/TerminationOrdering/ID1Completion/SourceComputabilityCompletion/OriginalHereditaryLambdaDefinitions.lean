module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaGuardLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambda
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original certificate path, with the replacement/root pair left in place. -/
def path : Program 4 := leftOf (.projection 2)

/-- Empty paths must reject here: the total head selector alone returns zero
at nil, which is also the original lambda-position number. -/
def pathNonempty : Program 4 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      (.composition InternalListCodec.nilTest (fun _ : Fin 1 => path)))
    (InternalLessThan.constantOne 4) (InternalAcceptance.constantZero 4)

def pathHeadLambda : Program 4 :=
  InternalApplicationStepPeel.same
    (.composition InternalListCodec.headCode (fun _ : Fin 1 => path))
    (InternalAcceptance.constantZero 4)

def lamPath : Program 4 :=
  InternalAcceptance.conjunction pathNonempty pathHeadLambda

/-- The original lambda prefix, using positionNumber lam = 0 and the SAME
replacement/root pair. Its inverse supplier is the accepted stripCertificate. -/
def prefixCertificate : Program 1 :=
  pairOf (consOf (InternalAcceptance.constantZero 1) InternalUnpair.left)
    InternalUnpair.right

/-- Stop at a non-lambda source or literal same-type bottom target. Every
control is normalized; a non-one lambda test takes the non-lambda branch. -/
def stop : Program 4 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      OriginalLambdaGuardLeaf.sourceLambda)
    (InternalLessThan.constantOne 4)
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
      OriginalLambdaGuardLeaf.sameBottom)

/-- Zero is failure. Every live state is a successor of the original nested
pair of [source,target,certificate,parameter], without a new term encoding. -/
def live : Program 4 :=
  .composition .succ (fun _ : Fin 1 =>
    pairOf (.projection 0)
      (pairOf (.projection 1) (pairOf (.projection 2) (.projection 3))))

def statePayload : Program 1 := InternalEqualityTest.predecessor
def stateSource : Program 1 := leftOf statePayload
def stateTarget : Program 1 := leftOf (rightOf statePayload)
def stateCertificate : Program 1 := leftOf (rightOf (rightOf statePayload))
def stateParameter : Program 1 := rightOf (rightOf (rightOf statePayload))

def atState (p : Program 4) : Program 1 :=
  .composition p ![stateSource,stateTarget,stateCertificate,stateParameter]

/-- An active step checks BOTH original path facts and the actual old leaf
at the actual body selectors, stripped certificate and extended parameter. -/
def advanceGuard (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction OriginalLambdaGuardLeaf.matchingTarget
    (InternalAcceptance.conjunction lamPath (OriginalLambdaGuardLeaf.childCheck oldStep))

def childLive : Program 4 :=
  .composition live
    ![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
      OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter]

/-- The outer control is the ORIGINAL raw state: zero fails and EVERY
successor is live, not merely state one. Stopped live states are fixed. An
active state advances only through the normalized exact-one advance guard. -/
def transition (oldStep : Program 4) : Program 1 :=
  InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
    (InternalAcceptance.branch
      (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (atState stop))
      (InternalAcceptance.branch
        (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize
          (atState (advanceGuard oldStep)))
        (InternalAcceptance.constantZero 1) (atState childLive))
      (.projection 0))

/-- Failure rejects. A live state accepts only when it has stopped, so a
live active state with an empty original path cannot bypass the child check. -/
def finish : Program 1 :=
  InternalAcceptance.branch (.projection 0) (InternalAcceptance.constantZero 1)
    (atState stop)

/-- Apply one unary transition per cell of the ORIGINAL encoded position
list. Front-cons commutation exposes the exact child run at its literal tail;
no numerical fuel, length estimate, padding, or replacement path is supplied. -/
def run (oldStep : Program 4) : Program 4 :=
  .composition (InternalRawListRepeat.repeatProgram (transition oldStep)) ![path,live]

def guard (oldStep : Program 4) : Program 4 :=
  .composition finish (fun _ : Fin 1 => run oldStep)

/-- The root pays the whole original old leaf, while every successful
advance pays that old leaf at the child. The continuation target below must
recover THIS SAME refined AST at its child, not just the one-level old leaf. -/
def refined (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction oldStep (guard oldStep)

abbrev accepted {alpha : Type} (p : Program 4)
    (source target certificate parameter : OTerm alpha) : Formula alpha :=
  OriginalConstructorLeaf.accepted p source target certificate parameter

abbrev LambdaNonbottom {alpha : Type}
    (source target certificate parameter : OTerm alpha) : Formula alpha :=
  OriginalLambdaGuardLeaf.LambdaNonbottom source target certificate parameter

def LeafHasGuard (oldStep leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((accepted leaf source target certificate parameter).imp
      (accepted (guard oldStep) source target certificate parameter)))

/-- All witnesses are connected to the SAME original four inputs. The
certificate-prefix graph retains the exact original replacement/root pair;
the last graph is acceptance by the SAME leaf, not a newly selected checker. -/
def ChildRecovered {alpha : Type} (leaf : Program 4)
    (source target certificate parameter sourceChild targetChild childStep childParam : OTerm alpha) :
    Formula alpha :=
  accepted OriginalLambdaGuardLeaf.matchingTarget source target certificate parameter ⊓
    (accepted lamPath source target certificate parameter ⊓
      (graph1 prefixCertificate certificate childStep ⊓
        (graph4 OriginalLambdaGuardLeaf.sourceBody sourceChild source target certificate parameter ⊓
          (graph4 OriginalLambdaGuardLeaf.targetBody targetChild source target certificate parameter ⊓
            (graph4 OriginalLambdaGuardLeaf.childCertificate childStep source target certificate parameter ⊓
              (graph4 OriginalLambdaGuardLeaf.childParameter childParam source target certificate parameter ⊓
                accepted leaf sourceChild targetChild childStep childParam))))))

/-- Generate all actual child witnesses internally. The premise contains
only original graph acceptance and the original lambda/nonbottom tests.
There is no caller-supplied body witness, calibrated semantic inference,
typing/window premise, path-length bound, or new reduction relation. -/
def InternalChildElimination (leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Delta
    (accepted leaf source target certificate parameter ⊓
      LambdaNonbottom source target certificate parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ sourceChild targetChild childStep childParam : OTerm beta,
    Nonempty (Derivation body Theta
      (ChildRecovered leaf (source.relabel j) (target.relabel j)
        (certificate.relabel j) (parameter.relabel j)
        sourceChild targetChild childStep childParam)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

/-- Explicit native raw-state specifications. These are total numerical
formulas, including malformed terms, certificates and contexts. They do not
replace the source numericStepTest or the original internal graph compiler. -/
def liveValue (v : List.Vector Nat 4) : Nat :=
  Nat.succ (Nat.pair (v.get 0) (Nat.pair (v.get 1) (Nat.pair (v.get 2) (v.get 3))))

def stateValues (state : Nat) : List.Vector Nat 4 :=
  let payload := state - 1
  List.Vector.ofFn ![(Nat.unpair payload).1,
    (Nat.unpair (Nat.unpair payload).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair payload).2).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair payload).2).2).2]

def childValues (v : List.Vector Nat 4) : List.Vector Nat 4 :=
  let domain := (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1
  let codomain := (Nat.unpair ((Nat.unpair (v.get 0)).1 - 1)).2
  List.Vector.ofFn ![
    Nat.pair codomain (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).2,
    Nat.pair codomain (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).2,
    OriginalLambdaCertificate.stripStep (v.get 2),
    Nat.pair (Nat.unpair (v.get 3)).1
      (Nat.succ (Nat.pair domain (Nat.unpair (v.get 3)).2))]

def stopValue (v : List.Vector Nat 4) : Nat :=
  if (Nat.unpair (Nat.unpair (v.get 0)).2).1 = 1 then
    if v.get 1 = Nat.pair (Nat.unpair (v.get 0)).1
      (Nat.pair 3 (Nat.unpair (v.get 0)).1) then 1 else 0
  else 1

def lamPathValue (v : List.Vector Nat 4) : Nat :=
  let code := (Nat.unpair (v.get 2)).1
  if code ≠ 0 ∧ (Nat.unpair (code - 1)).1 = 0 then 1 else 0

def matchingTargetValue (v : List.Vector Nat 4) : Nat :=
  if (Nat.unpair (Nat.unpair (v.get 1)).2).1 = 1 ∧
    (Nat.unpair (v.get 1)).1 = (Nat.unpair (v.get 0)).1 ∧
    (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).1 =
      (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1 then 1 else 0

def transitionValue (oldStep : Program 4) (state : Nat) : Nat :=
  if state = 0 then 0 else
    let v := stateValues state
    if stopValue v = 1 then state else
      if matchingTargetValue v = 1 ∧ lamPathValue v = 1 ∧
        evaluate oldStep (childValues v) = 1 then liveValue (childValues v) else 0

def finishValue (state : Nat) : Nat :=
  if state = 0 then 0 else stopValue (stateValues state)

/-- Only the oldStep field changes. This is not yet a global selection or
lambda computability theorem; a future theorem must preserve the complete
previous Package and all consumers at ONE final tuple. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.oldStep }

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambda
