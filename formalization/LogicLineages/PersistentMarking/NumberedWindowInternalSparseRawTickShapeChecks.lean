module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTickProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparseRawTick (liveTick chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeLiveProof (liveShape)
open NumberedWindowInternalSparseRawTickShapeTickProof (tickShape)

theorem exact_OpenLiveTickShape : ExactOpenLiveTickShape := by
  intro body p other α out xs
  obtain ⟨d⟩ := liveShape (body := body)
    (Γ := [programGraph (liveTick p other) out xs]) p other out xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem exact_OpenTickShape : ExactOpenTickShape := by
  intro body p other α flag frame out
  let g := programGraph (chosenTick p other) out ![stateTerm flag frame]
  obtain ⟨d⟩ := tickShape (body := body) (Γ := [g]) p other flag frame out
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenLiveTickShape
#print axioms exact_OpenTickShape
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeChecks
