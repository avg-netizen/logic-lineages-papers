module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ActualOriginalClassContextObserverCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalTransparentMinimum.ClassTestCalibrated n arity
    (OriginalClassContextObserver.classTest p H G W P)
def ActualOriginalClassContextObserverHit : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3), OriginalClassContextObserver.HitLaw p H G W P
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverTargets
