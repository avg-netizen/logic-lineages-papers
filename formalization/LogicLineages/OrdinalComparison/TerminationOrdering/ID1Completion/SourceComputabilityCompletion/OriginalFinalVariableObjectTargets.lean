module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectTargets
open UniformCertificateCompletion OriginalFinalVariableObject
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualOriginalFinalVariableObjectCalibration : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs), CalibrationLaw p

def ActualOriginalFinalVariableObjectExposure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs), ExposureLaw p

def ActualOriginalFinalVariableObjectFixedness : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), FixednessLaw guard p

def ActualOriginalFinalVariableObjectCancellation : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), CancellationLaw guard p

def ActualOriginalFinalVariableObjectRankPreservation : Prop :=
  ∀ (guard : Program 1) (p : GlobalSourcePackage.Inputs), RankLaw guard p

def ActualOriginalFinalVariableObjectSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (guard : Program 1), Properties n arity p guard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectTargets
