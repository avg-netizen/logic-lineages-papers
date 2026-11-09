module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationTargets
open Source
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterObject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Extract the original step slice from its already-selected global leaf,
at ANY raw parameter with the actual decoded Context and Object Gamma.
There is no canonical-parameter, source-validity, subtype-closure, endpoint
or accepted-certificate hypothesis. This does not select another Program. -/
def ActualOriginalDecodedStepLeafCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4),
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode (Nat.unpair parameter).1 = some ctx →
  ∀ Gamma : List Ty,
  (∀ value : Nat, parameterObject value parameter = some (Gamma,value)) →
  InternalParameterizedApplicationStepChecker.StepCalibratedAt
    n arity ctx.1.1 ctx.1.2 Gamma ctx.2 oldStep parameter

/-- One globally calibrated tuple/step/shape choice precedes EVERY raw
parameter and decoded source window. One actual Gamma covers ALL endpoints,
types and original certificates at that parameter. Successful Context decode
and subtype closure restrict only the window, never the numeric inputs.

This is the native decoded-window prerequisite for the original all-input
Outer positive dispatcher. It is not calibration of malformed/nonclosed
fallbacks, selection of a complete source package, an internal derivation,
or the closed all-term ID1 endpoint. Use the SAME OuterSelection.data when
assembling that later source; do not normalize its membership a second time. -/
def ActualOriginalRuntimePositiveCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data)
    (oldStep : Program 4) (bottom measure : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  PositiveGuard.ShapeCalibrated n arity bottom measure →
  ∀ (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode (Nat.unpair parameter).1 = some ctx →
  SubtypeClosed (fun typ => typ ∈ ctx.1.2) →
  ∃ Gamma : List Ty,
    RuntimePositiveCalibration.Calibrated n arity data oldStep bottom measure parameter ctx Gamma

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibrationTargets
