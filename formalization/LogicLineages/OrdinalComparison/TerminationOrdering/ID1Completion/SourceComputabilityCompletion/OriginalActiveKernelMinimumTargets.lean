module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumTargets
open UniformCertificateCompletion OriginalActiveKernelMinimum
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalActiveKernelMinimumCoherence : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3), CoherenceLaw p H G W P

def ActualOriginalActiveKernelMinimumIdempotence : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3), IdempotenceLaw p H G W P

def ActualOriginalActiveKernelMinimumRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  Properties n arity p H G W P

def ActualOriginalActiveKernelMinimumSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
    Properties n arity p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumTargets
