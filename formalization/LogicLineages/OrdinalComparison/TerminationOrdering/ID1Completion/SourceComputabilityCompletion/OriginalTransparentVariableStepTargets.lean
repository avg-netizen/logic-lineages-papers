module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepTargets
open UniformCertificateCompletion OriginalTransparentVariableStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalTransparentVariableStepEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  ∀ v : List.Vector Nat 4, evaluate (refineInputs p).oldStep v = evaluate p.oldStep v

def ActualOriginalTransparentVariableStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  GlobalSourcePackage.InputsCalibrated n arity (refineInputs p)

def ActualOriginalTransparentVariableStepIntroduction : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4), IntroductionLaw source oldStep

def ActualOriginalTransparentVariableStepRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalActiveKernelMinimum.Properties n arity (refineInputs p) H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepTargets
