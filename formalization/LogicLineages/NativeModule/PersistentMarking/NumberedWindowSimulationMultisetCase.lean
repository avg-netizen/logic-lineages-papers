module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationSourceSplitProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationPlacementTraces

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationMultisetCase
open LiteralDerivationTree
open NumberedWindowSyntax NumberedWindowTupleTargets NumberedWindowOrdinaryTranslation
open NumberedWindowSimulationData NumberedWindowSimulationJobs
open NumberedWindowSimulationSourceSplitProof NumberedWindowSimulationPlacement
open NumberedWindowTraceTypingProof (argsStart)

theorem replace (S : Spine.Signature) (K : List Ty)
    (source kept removed target matched added : Spine.Args)
    (hs : Spine.Split source kept removed) (ht : Spine.Split target matched added)
    (hne : Spine.Nonempty removed)
    (m : Tree S (.matching kept matched)) (c : Tree S (.coverage removed added))
    (ihM : Job S K m) (ihC : Job S K c) :
    Job S K (.multisetReplace source kept removed target matched added hs ht hne m c) := by
  intro h n As hn hRep
  have hb : max (budget m) (budget c) ≤ n := hn
  have hm : Foot K m := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_left _ hp))
  have hc : Foot K c := fun ρ hp => h ρ (List.mem_append_right _ (List.mem_append_right _ hp))
  obtain ⟨Ks,Rs,hKs,hRs,hsPerm⟩ := realizedSplit hs n As hRep
  obtain ⟨startM,finalM,hp,hM,⟨pM⟩⟩ :=
    ihM hm n Ks (Nat.le_trans (Nat.le_max_left _ _) hb) hKs
  obtain ⟨startC,finalC,hC,hOrigin,⟨pC⟩⟩ :=
    ihC hc n Rs (Nat.le_trans (Nat.le_max_right _ _) hb) hRs
  obtain ⟨place,hQuote⟩ := quotedPlacement ht finalM finalC hM hC
  have hTrace := NumberedWindowSimulationPlacementTraces.both place pM pC
  have hTargetPerm := NumberedWindowSimulationPlacementProof.permutation place (argsStart pM) (argsStart pC)
  refine ⟨_,_,hQuote,?_,hTrace⟩
  exact ⟨startM.toList,Rs.toList,startC.toList,hsPerm.trans (hp.append_right _),
    hTargetPerm,realizedNonempty hRs hne,hOrigin⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationMultisetCase
