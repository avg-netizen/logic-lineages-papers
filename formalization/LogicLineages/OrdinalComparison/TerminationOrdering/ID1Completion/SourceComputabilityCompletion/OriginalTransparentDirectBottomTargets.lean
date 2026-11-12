module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open OriginalTransparentDirectBottom
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalDirectBottomEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  ∀ v : List.Vector Nat 4, evaluate (refineInputs p).oldStep v = evaluate p.oldStep v

def ActualOriginalDirectBottomCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  GlobalSourcePackage.InputsCalibrated n arity (refineInputs p)

/-- Internal raw exact-certificate introduction, separate from native calibration. -/
def ActualOriginalDirectBottomIntroduction : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (s t cert parameter typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premises source s t cert parameter typ).imp
      (graph4 (refined source oldStep) InternalOriginalStepGuard.one s t cert parameter)))

/-- The whole unchanged closed leaf for the CONCRETE original universe
source decoder only. Actual source acceptance must discharge bottom-tag
consistency and the spine obligation; neither is an extra premise. No native
calibration-to-internal reflection, supplied tag, or spine positivity oracle. -/
def ActualOriginalConcreteDirectBottomClosedLeaf : Prop :=
  ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
    (endpoint : Program 6) (window : Program 1) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (s t cert parameter typ : OTerm alpha),
  let source := OriginalUniverseDecoder.source H G M W
  Nonempty (Derivation body Delta
    ((Premises source s t cert parameter typ).imp
      (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (refined source oldStep))
        InternalOriginalStepGuard.one s t cert parameter)))

def ActualOriginalDirectBottomRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalActiveKernelMinimum.Properties n arity (refineInputs p) H G W P
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
