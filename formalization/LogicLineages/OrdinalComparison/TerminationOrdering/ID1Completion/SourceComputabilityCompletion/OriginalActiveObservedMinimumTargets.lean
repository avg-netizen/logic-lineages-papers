module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual postguard least-hit minimality, for arbitrary original programs. -/
def ActualOriginalActiveObservedMinimumInternalMinimum : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3), OriginalActiveObservedMinimum.MinimumLaw p H G W P

/-- Reconstruct all laws and the complete previous Package at the supplied
tuple, using only the original calibration hypotheses. No class kernel,
coherence, minimum or final-rank law is assumed by the caller. -/
def ActualOriginalActiveObservedMinimumRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalActiveObservedMinimum.Properties n arity p H G W P

/-- Select the shared tuple once, before every original source window and
ambient Gamma represented by the independently quantified internal laws. -/
def ActualOriginalActiveObservedMinimumSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3), OriginalActiveObservedMinimum.Properties n arity p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumTargets
