module
public import LogicLineages.CartierObserverCurrent.FullResidueObserverTargets
public import LogicLineages.CartierObserverCurrent.FiniteProfileProof
public import LogicLineages.CartierObserverCurrent.ProfileTransitionsProof
public import LogicLineages.CartierObserverCurrent.ProfileOutputProof
public import LogicLineages.CartierObserverCurrent.AllWordObserverProof
public import LogicLineages.CartierObserverCurrent.SourceObserverProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullResidueObserver

theorem completeResidueObserver : Targets.CompleteResidueObserver := by
  exact ⟨GeometricState.actualBaseEquivalence,
    FiniteProfile.actualGeometricBijection,
    FiniteProfile.actualFiniteProfile,
    FiniteProfile.actualFiniteState,
    ProfileTransitions.actualIntertwining,
    ProfileTransitions.compatiblePreservation,
    ProfileTransitions.actualBaseSquare,
    ProfileOutput.outputDescent,
    ProfileOutput.actualBaseOutput,
    AllWordObserver.profileExecution,
    AllWordObserver.compatibleExecution,
    AllWordObserver.baseObservation,
    SourceObserver.presentedExpansion,
    SourceObserver.exactSourceContinuations⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullResidueObserver
end LogicLineages.CartierObserverCurrent.FullResidueObserver
