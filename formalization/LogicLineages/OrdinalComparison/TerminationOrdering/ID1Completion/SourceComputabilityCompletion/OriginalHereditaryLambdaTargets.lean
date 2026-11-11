module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryLambda
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact total raw-state and child-selector equations. No source decoding or
typing assumption is allowed, and the original certificate/context positions
are retained even on malformed inputs. -/
def ActualOriginalHereditaryLambdaRawCalibration : Prop :=
  (∀ certificate : Nat,
    evaluate prefixCertificate (List.Vector.ofFn ![certificate]) =
      OriginalLambdaCertificate.liftStep certificate) ∧
  (∀ v : List.Vector Nat 4,
    evaluate path v = (Nat.unpair (v.get 2)).1 ∧
      evaluate live v = liveValue v ∧
      evaluate OriginalLambdaGuardLeaf.sourceBody v = (childValues v).get 0 ∧
      evaluate OriginalLambdaGuardLeaf.targetBody v = (childValues v).get 1 ∧
      evaluate OriginalLambdaGuardLeaf.childCertificate v = (childValues v).get 2 ∧
      evaluate OriginalLambdaGuardLeaf.childParameter v = (childValues v).get 3 ∧
      evaluate childLive v = liveValue (childValues v)) ∧
  (∀ state : Nat,
    evaluate stateSource (List.Vector.ofFn ![state]) = (stateValues state).get 0 ∧
      evaluate stateTarget (List.Vector.ofFn ![state]) = (stateValues state).get 1 ∧
      evaluate stateCertificate (List.Vector.ofFn ![state]) = (stateValues state).get 2 ∧
      evaluate stateParameter (List.Vector.ofFn ![state]) = (stateValues state).get 3) ∧
  (∀ (p : Program 4) (state : Nat),
    evaluate (atState p) (List.Vector.ofFn ![state]) = evaluate p (stateValues state))

/-- All controls have explicit total numerical behavior. In particular nil
does not pass lamPath, failed/active final states reject, stopped states stay
fixed, and every successful advance pays matching, prefix and old-child tests. -/
def ActualOriginalHereditaryLambdaControlCalibration : Prop :=
  (∀ v : List.Vector Nat 4,
    evaluate stop v = stopValue v ∧
      evaluate lamPath v = lamPathValue v ∧
      evaluate OriginalLambdaGuardLeaf.matchingTarget v = matchingTargetValue v) ∧
  (∀ (oldStep : Program 4) (v : List.Vector Nat 4),
    evaluate (advanceGuard oldStep) v =
      if matchingTargetValue v = 1 ∧ lamPathValue v = 1 ∧
        evaluate oldStep (childValues v) = 1 then 1 else 0) ∧
  (∀ (oldStep : Program 4) (state : Nat),
    evaluate (transition oldStep) (List.Vector.ofFn ![state]) = transitionValue oldStep state) ∧
  (∀ state : Nat,
    evaluate finish (List.Vector.ofFn ![state]) = finishValue state)

/-- Generic ORIGINAL internal graph law needed for failure absorption and
stopped-state preservation. A real transition fixed point repeats to itself
on EVERY raw encoded list, without a native interpretation or fuel premise. -/
def ActualOriginalHereditaryLambdaRepeatFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1)
    (alpha : Type) (Delta : List (Formula alpha)) (state code : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 transition state state).imp
      (InternalRawListRepeat.repeatGraph transition state code state)))

/-- The original nonempty/head-zero path and the actual strip output restore
the original certificate INTERNALLY. All replacement/root coordinates are
preserved; no decoded certificate or user-supplied path witness is assumed. -/
def ActualOriginalHereditaryLambdaInternalPrefix : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter childStep : OTerm alpha),
  Nonempty (Derivation body Delta
    ((accepted lamPath source target certificate parameter ⊓
      graph4 OriginalLambdaGuardLeaf.childCertificate childStep source target certificate parameter).imp
      (graph1 prefixCertificate certificate childStep)))

/-- Pure original-AST factor laws for arbitrary oldStep. This target must be
proved in the original calculus independently of native calibration. -/
def ActualOriginalHereditaryLambdaInternalFactors : Prop :=
  ∀ oldStep : Program 4,
    OriginalConstructorLeaf.OriginalFactor oldStep (refined oldStep) ∧
      LeafHasGuard oldStep (refined oldStep)

/-- Full-output equality on ALL four-input raw vectors, including failed
decodings and malformed contexts. The only assumption is the original leaf
calibration. Accepted lambda descent must retain the SAME certificate and
its literal suffix, not use a completeness-selected child certificate. -/
def ActualOriginalHereditaryLambdaRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4),
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ v : List.Vector Nat 4, evaluate (refined oldStep) v = evaluate oldStep v

/-- The ultimate internal closure contract: recover acceptance by the SAME
refined AST at the actual original lambda body selectors, exact stripped
certificate and extended runtime parameter. No additional witness premise,
native-to-internal reflection, typing/window oracle or new relation occurs. -/
def ActualOriginalHereditaryLambdaInternalChildElimination : Prop :=
  ∀ oldStep : Program 4, InternalChildElimination (refined oldStep)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaTargets
