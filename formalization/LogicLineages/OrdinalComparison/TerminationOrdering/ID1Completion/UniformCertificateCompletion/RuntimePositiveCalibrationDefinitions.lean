module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibration
open Source
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterObject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native calibration at the caller's UNCHANGED raw parameter. One actual
Object-decoded Gamma serves the selected endpoint, old step leaf, normalized
step, guarded step, original quotient edge and both-guard positive checker.
No raw Context re-encoding equation or extra certificate field is introduced.
The separate target validator retains unrestricted packed-target semantics. -/
structure Calibrated (n : Nat) (arity : Fin n → Nat) (data : Data)
    (oldStep : Program 4) (bottom measure : Program 1) (parameter : Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty) : Prop where
  objectSlice : ∀ value : Nat, parameterObject value parameter = some (Gamma,value)
  targetValidity : ∀ value : Nat,
    evaluate (InternalOriginalUniformDescentSelection.targetValidity data)
        (List.Vector.ofFn ![value,parameter]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value
  endpoint : InternalParameterizedApplicationStepChecker.EndpointCalibratedAt
    n arity ctx.1.1 ctx.1.2 Gamma
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data) parameter
  leaf : InternalParameterizedApplicationStepChecker.StepCalibratedAt
    n arity ctx.1.1 ctx.1.2 Gamma ctx.2 oldStep parameter
  selectedStep : InternalParameterizedApplicationStepChecker.StepCalibratedAt
    n arity ctx.1.1 ctx.1.2 Gamma ctx.2
    (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) parameter
  guardedStep : InternalParameterizedApplicationStepChecker.StepCalibratedAt
    n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (stepChecker data oldStep) parameter
  sourceRepresentative : ∀ value : Nat,
    evaluate (UniformCertificateCompletion.sourceRepresentative data)
        (List.Vector.ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.sourceRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value
  targetRepresentative : ∀ value : Nat,
    evaluate (UniformCertificateCompletion.targetRepresentative data)
        (List.Vector.ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value
  edge : InternalParameterizedPathChecker.EdgeCalibrated
    n arity ctx.1.1 ctx.1.2 Gamma ctx.2 (edgeChecker data oldStep) parameter
  positive : ∀ x y certificate : Nat,
    evaluate (Outer.rawPositive data oldStep bottom measure)
        (List.Vector.ofFn ![x,y,certificate,parameter]) =
      if NumberedQuotientPathCertificates.positivePathTest
        n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y certificate then 1 else 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePositiveCalibration
