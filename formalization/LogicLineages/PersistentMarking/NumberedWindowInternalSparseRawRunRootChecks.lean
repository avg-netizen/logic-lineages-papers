module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawTick (rootCall)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawRunRootTargets
open NumberedWindowInternalSparseRawRunRootProof (tickRoot rootRunAccept rootRunRecover)

theorem exact_OpenRootTick : ExactOpenRootTick := by
  intro body p other α flag q payload r c
  let call := programGraph (rootCall p) c ![q,rootWitnessTerm payload,r]
  obtain ⟨d⟩ := tickRoot (body := body) (Γ := [call]) p other flag q payload r c
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem exact_OpenRootOwnRun : ExactOpenRootOwnRun := by
  intro body p other α q payload r
  let accepts := programGraph p (suc z) ![q,payload,r]
  let run := programGraph (ownRun p other) (suc z) ![q,rootWitnessTerm payload,r]
  obtain ⟨forward⟩ := rootRunAccept (body := body) (Γ := [accepts]) p other q payload r
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := rootRunRecover (body := body) (Γ := [run]) p other q payload r
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

#print axioms exact_OpenRootTick
#print axioms exact_OpenRootOwnRun
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootChecks
