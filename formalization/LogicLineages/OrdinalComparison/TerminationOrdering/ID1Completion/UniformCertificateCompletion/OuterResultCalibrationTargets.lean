module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationTargets
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original valid-window/typed-function/typed-argument/same-Gamma
activation, for every raw five-vector. No output or success premise occurs. -/
def ActualOriginalOuterResultActivationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (old : JointGammaComputability.Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  JointGammaComputability.Calibrated old n arity →
  ∀ v : List.Vector Nat 5,
    evaluate (Outer.resultActivation old (OuterSelection.data base window) window) v =
      ApplicationDomain.activationValue n arity v

/-- Independent FULL original Option success of the literal paired branch
and dispatcher, including a successful numeric zero. No oldResult calibration
is needed on the active branch. H=1 is not used as an Option-success premise;
original object/context/type/domain semantics must establish success. -/
def ActualOriginalOuterActiveResultSuccess : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (old : JointGammaComputability.Data) (oldVertex oldResult : Program 5),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  JointGammaComputability.Calibrated old n arity →
  (∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v) →
  ∀ v : List.Vector Nat 5,
    evaluate (Outer.resultActivation old (OuterSelection.data base window) window) v = 1 →
    ApplicationResultBuilder.resultOption n arity v =
      some (evaluate (Outer.resultBranch
        (Path.vertex (OuterSelection.data base window) window oldVertex)) v) ∧
    ApplicationResultBuilder.resultOption n arity v =
      some (evaluate (Outer.result old (OuterSelection.data base window) window oldVertex oldResult) v) ∧
    ApplicationResultBuilder.successValue n arity v = 1 ∧
    (evaluate (Outer.result old (OuterSelection.data base window) window oldVertex oldResult) v = 0 →
      ApplicationResultBuilder.resultOption n arity v = some 0)

/-- Original all-input result and three-field application calibration. The
complete old result remains a replaceable global input and is retained on
ALL inactive vectors, not only valid contexts or successful decodings. -/
def ActualOriginalOuterResultComputabilityCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (old : JointGammaComputability.Data) (oldVertex oldResult : Program 5),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  JointGammaComputability.Calibrated old n arity →
  (∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v) →
  (∀ v : List.Vector Nat 5, evaluate oldResult v = ApplicationResultBuilder.resultValue n arity v) →
  OuterResultCalibration.Calibrated n arity base window old oldVertex oldResult

/-- Pure AST fallback equations with NO calibration, typing, decoding,
window, or success assumptions. The full original five/six input vectors
and whole old result/application outputs survive inactive dispatch. -/
def ActualOriginalOuterResultApplicationFallback : Prop :=
  ∀ (data : Data) (window : Program 1) (old : JointGammaComputability.Data)
    (oldVertex oldResult : Program 5),
  (∀ v : List.Vector Nat 5,
    evaluate (Outer.resultActivation old data window) v = 0 →
    evaluate (Outer.result old data window oldVertex oldResult) v = evaluate oldResult v) ∧
  (∀ v : List.Vector Nat 6,
    evaluate (Outer.resultActivation old data window)
      (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4]) = 0 →
    evaluate (Outer.computability old data window oldVertex oldResult).application v =
      evaluate old.application v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultCalibrationTargets
