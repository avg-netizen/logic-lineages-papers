module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (ownState ownRun)
open NumberedWindowInternalSparseRawRunSuccessTargets
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal terminalOwnRun)

theorem exact_OpenOwnRunSuccessTerminal : ExactOpenOwnRunSuccessTerminal := by
  intro body p other α q w r k
  let run := programGraph (ownRun p other) (suc k) ![q,w,r]
  let terminal := programGraph (ownState p other) (stateTerm (suc k) z) ![q,w,r]
  obtain ⟨forward⟩ := ownRunTerminal (body := body) (Γ := [run]) p other k ![q,w,r]
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := terminalOwnRun (body := body) (Γ := [terminal]) p other k ![q,w,r]
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

#print axioms exact_OpenOwnRunSuccessTerminal
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessChecks
