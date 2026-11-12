module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionTargets
open UniformCertificateCompletion OriginalClassContextAllPositionSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOutput : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1)
  (W : Program 2) (P : Program 3), OutputLaw p H G W P

def ActualRetention : Prop :=
  ∀ n (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P → Properties n arity p H G W P

def ActualSelection : Prop := ∀ n (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    Properties n arity p H G W P
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionTargets
