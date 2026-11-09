module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationTargets
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Pay the concrete shape supplier: the actual bottom recognizer and full
flag/depth measure, for EVERY original proper typed term and ambient Gamma.
No abstract shape correctness premise reaches the next construction. -/
def ActualOriginalConcreteShapeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  PositiveGuard.ShapeCalibrated n arity
    SourceComputabilityCompletion.BottomRepresentative.bottomTest
    SourceComputabilityCompletion.BottomSpineMeasure.measure

/-- The literal Object positive dispatcher on ALL original four-vectors.
The SAME selected tuple and complete oldPositive precede every raw context,
source/target Object and supplied original path certificate. Cross-Gamma
inputs are included. No successful Context decode, source validity, target
validity, canonical input, accepted certificate or fixed Gamma is a premise. -/
def ActualOriginalOuterPositiveCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (oldStep oldPositive : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  (∀ v : List.Vector Nat 4,
    evaluate oldPositive v = ContextUniform.positiveValue n arity v) →
  ∀ v : List.Vector Nat 4,
    evaluate (OuterSourceCalibration.positive base window oldStep oldPositive) v =
      ContextUniform.positiveValue n arity v

/-- Native calibration of all FOUR fields of the literal final source.
Its original Gamma, source/target typing, tag and valid-window layers remain
present. The old multiset/direct fields are copied, not reselected per window.
Global input calibration is explicit; this is not yet a witness existential
or a claim of internal constructor/multiset/lambda/substitution derivations. -/
def ActualOriginalOuterSourceCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (oldStep : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  ContextUniform.Calibrated oldSrc n arity →
  JointGammaComputability.Calibrated oldComp n arity →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ContextUniform.Calibrated
    (OuterSelection.source oldSrc oldComp base oldStep window) n arity

/-- The accepted literal Outer lift receives ALL original five-vectors,
including malformed/nonclosed Contexts, every Object and every path code.
Its parameter is pair(rawContext,left(argumentObject)); the certificate and
raw argument remain separate. The actual Object decoder supplies Gamma.
The complete oldVertex fallback and original path defaults are retained.

OuterSelection.lift itself has no oldLift argument. This target neither
alters that accepted AST nor claims the oldLift dispatcher already exists. -/
def ActualOriginalOuterObjectLiftCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (oldVertex : Program 5),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v) →
  ∀ v : List.Vector Nat 5,
    evaluate (OuterSelection.lift base window oldVertex) v =
      ApplicationCertificateLiftPath.pathValue n arity v

/-- Unconditional AST preservation. Zero window activation retains the
COMPLETE oldPositive output on the unchanged four-vector. The literal final
source copies the same globally supplied multiset/direct Programs. These
equalities have no calibration, decoding, validity or success hypotheses. -/
def ActualOriginalOuterPositiveSourceFallback : Prop :=
  ∀ (data : Data) (rawScalar : Program 2) (oldStep : Program 4)
    (bottom measure window : Program 1) (oldPositive : Program 4)
    (oldSrc : SourcePresentation.Data) (oldComp : JointGammaComputability.Data),
  (∀ v : List.Vector Nat 4,
    evaluate window (List.Vector.ofFn ![v.get 0]) = 0 →
    evaluate (Outer.positive (Outer.rawPositive data oldStep bottom measure)
      window oldPositive) v = evaluate oldPositive v) ∧
  (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window).multiset =
    oldSrc.multiset ∧
  (Outer.source oldSrc oldComp data rawScalar oldStep bottom measure window).direct =
    oldSrc.direct

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSourceCalibrationTargets
