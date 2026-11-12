module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalAllPositionStructuralTraversalDefinitions
/-- Calibration of the literal pre-key, observed selected minimum and twice-guarded
traversal input. These are not identified with the earlier raw-minimum tuple. -/
def NativePreparation (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity (OriginalStructuralClassKeyDefinitions.inputs p H G W) ∧
  GlobalSourcePackage.InputsCalibrated n arity (minimumInputs p H G W P) ∧
  GlobalSourcePackage.InputsCalibrated n arity (refined p H G W P)

/-- Both the earlier minimum package and freshly reconstructed rank/full inherited
package coexist. The latter is at our actual minimumInputs followed by its own
rank/transparent/variable refinement, not the raw minimum from the former. -/
def Retained (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) : Prop :=
  NativePreparation n arity p H G W P ∧
  OriginalClassContextAllPositionSelection.Properties n arity
    (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P ∧
  OriginalFinalGuardedRank.Properties n arity (minimumInputs p H G W P) H G W

def ActualRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  Retained n arity p H G W P

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionTargets
