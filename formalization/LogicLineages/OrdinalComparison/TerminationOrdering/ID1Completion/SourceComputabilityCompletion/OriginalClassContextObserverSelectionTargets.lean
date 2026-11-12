module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionTargets
open UniformCertificateCompletion OriginalClassContextObserverSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def ActualOriginalClassContextObserverOutput : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3), OutputLaw p H G W P
def ActualOriginalClassContextObserverRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P → Properties n arity p H G W P
def ActualOriginalClassContextObserverSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    Properties n arity p H G W P
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionTargets
