module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationJobs
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationDomainProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationWindowProof
public import LogicLineages.NativeModule.PersistentMarking.SpineShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets
open NumberedWindowSimulationJobs

theorem window {S K q Q τ n} (h : Spine.PaperTerm S q τ)
    (hk : SymbolicAdmissible K q) (hQ : Realizes n q Q) :
    InWindow S K E q.type Q := by
  rw [SpineShiftProof.annotationExact E q τ h.1]
  exact NumberedWindowRealizationWindowProof.inWindow S K E τ n q Q h.1 h.2 hk hQ

theorem paperType {S q τ} (h : Spine.PaperTerm S q τ) : q.type = τ :=
  SpineShiftProof.annotationExact E q τ h.1

theorem realizesAtType {C q Q τ n} (h : Realizes n q Q) (hQ : Typed C Q τ) :
    q.type = τ := by
  exact (NumberedWindowRealizationShapeProof.termShape h).1.symm.trans
    (NumberedWindowApplicationDomainProof.annotation hQ)

end LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof
