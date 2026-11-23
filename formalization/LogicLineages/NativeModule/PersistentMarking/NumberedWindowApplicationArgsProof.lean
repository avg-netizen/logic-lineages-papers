module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationWindowProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationArgsProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets NumberedWindowApplicationTargets

theorem realized : RealizedCallArgs := by
  intro S K C σ τ args As n hCall
  induction hCall generalizing As with
  | nil =>
    intro _ _ hr
    cases hr
    exact ⟨[],rfl,rfl,.nil⟩
  | cons hHead hTail ih =>
    intro hv hu hr
    cases hr with
    | cons hRep hReps =>
      have ha := NumberedWindowRealizationWindowProof.inWindow S K C _ n _ _ hHead hv.1
        (fun ρ hρ => hu ρ (List.mem_append_left _ hρ)) hRep
      obtain ⟨ds,hd,hl,hw⟩ := ih _ hv.2 (fun ρ hρ => hu ρ (List.mem_append_right _ hρ)) hReps
      exact ⟨_ :: ds,by simp only [ArrowPrefix,hd],
        by simp only [List.length_cons,Spine.Args.length,hl,Nat.add_comm],.cons ha hw⟩

end LogicLineages.PersistentMarking.NumberedWindowApplicationArgsProof
