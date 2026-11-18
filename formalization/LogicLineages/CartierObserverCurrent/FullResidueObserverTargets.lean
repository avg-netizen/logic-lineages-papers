module
public import LogicLineages.CartierObserverCurrent.FiniteProfileTargets
public import LogicLineages.CartierObserverCurrent.GeometricStateTargets
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsTargets
public import LogicLineages.CartierObserverCurrent.ProfileOutputTargets
public import LogicLineages.CartierObserverCurrent.AllWordObserverTargets
public import LogicLineages.CartierObserverCurrent.SourceObserverTargets

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullResidueObserver.Targets

/-- Exact mathematical numbered complete residue-profile observer, with genuine
geometric states, all poles, actual finite profiles, both maps and every source continuation. -/
def CompleteResidueObserver : Prop :=
  GeometricState.Targets.ActualBaseEquivalence ∧
  FiniteProfile.Targets.ActualGeometricBijection ∧
  FiniteProfile.Targets.ActualFiniteProfile ∧
  FiniteProfile.Targets.ActualFiniteState ∧
  ProfileTransitions.Targets.ActualIntertwining ∧
  ProfileTransitions.Targets.CompatiblePreservation ∧
  ProfileTransitions.Targets.ActualBaseSquare ∧
  ProfileOutput.Targets.OutputDescent ∧
  ProfileOutput.Targets.ActualBaseOutput ∧
  AllWordObserver.Targets.ProfileExecution ∧
  AllWordObserver.Targets.CompatibleExecution ∧
  AllWordObserver.Targets.BaseObservation ∧
  SourceObserver.Targets.PresentedExpansion ∧
  SourceObserver.Targets.ExactSourceContinuations
end LogicLineages.CartierObserverCurrent.FullResidueObserver.Targets
