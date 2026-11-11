module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeTargets
open UniformCertificateCompletion OriginalRankGuardedRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalRankGuardedRepresentativeLiteralFields : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    LiteralFields p H G W

/-- All-vector redundancy is proved from the SAME original calibrated tuple
and decoder programs. No preselected window or successful decode is assumed. -/
def ActualOriginalRankGuardedRepresentativeNativePreparation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
      (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  NativePreparation n arity p H G W

/-- Arbitrary Program tuples and internal arithmetic inputs; native calibration
is absent. The actual original window and transparent source graphs pay activity. -/
def ActualOriginalRankGuardedRepresentativeInternalRank : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    RankLaw p H G W

/-- Universal reconstruction at the SAME explicitly constructed tuple. -/
def ActualOriginalRankGuardedRepresentativeRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
      (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  Retained n arity p H G W

/-- One original tuple and H/G/W before all runtime windows, contexts and
raw inputs, with the COMPLETE previous Package at the same final pipeline. -/
def ActualOriginalRankGuardedRepresentativeSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
      Properties n arity p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeTargets
