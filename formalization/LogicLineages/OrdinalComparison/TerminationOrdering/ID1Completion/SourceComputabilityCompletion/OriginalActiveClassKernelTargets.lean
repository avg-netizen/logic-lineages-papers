module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelTargets
open UniformCertificateCompletion OriginalActiveClassKernel
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original classValue calibration on every input vector, including
inactive/malformed cases, using only original calibration hypotheses. -/
def ActualOriginalActiveClassKernelCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalTransparentMinimum.ClassTestCalibrated n arity (classTest p H G W P)

def ActualOriginalActiveClassKernelCharacterization : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3), CharacterizationLaw p H G W O P

def ActualOriginalActiveClassKernelHitDomain : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3), HitDomainLaw p H G W O P

def ActualOriginalActiveClassKernelRowCoherence : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3), RowCoherenceLaw p H G W O P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelTargets
