module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedClassDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Preserve the original class predicate on EVERY raw input vector. Only
the original window calibration is required; off-domain inputs retain P. -/
def ActualOriginalActiveObservedRankCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  (∀ v, evaluate p.window v = GuardCalibration.validWindowValue n v) →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalTransparentMinimum.ClassTestCalibrated n arity
    (OriginalActiveObservedClass.classTest p H G W
      OriginalRawSyntaxTransport.variableRankPackedRaw P)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationTargets
