module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationOccurrenceProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceContextsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationHeadSupport
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowOrdinaryTranslation
open NumberedWindowTraceAlgebra NumberedWindowPreservationTargets
open NumberedWindowSimulationJobs NumberedWindowSimulationOccurrenceProof

theorem headGuard {S K f bs} (h : Spine.PaperTerm S (.head f bs) f.result)
    (hs : SymbolicAdmissible K (.head f bs)) : HeadInWindow S K f :=
  ⟨h.2.1,fun t ht => hs t (List.mem_append_left _ ht)⟩

theorem targetTypes {S f bs} (h : Spine.PaperTerm S (.head f bs) f.result) : types bs = f.arguments := by
  cases h.1 with
  | head hb => exact paperBaseTypes E bs _ hb

theorem targetTrace {S K f bs first last}
    (h : Spine.PaperTerm S (.head f bs) f.result)
    (path : ArgsTrace S K E (types bs) first last) :
    Nonempty (TypedTrace S K E f.result (.ordinary f first) (.ordinary f last)) := by
  rw [targetTypes h] at path
  obtain ⟨out,_⟩ := NumberedWindowTraceContextsProof.ordinaryBase S K E f _ _ path
  exact ⟨out⟩

theorem quoteHead {f bs As} (h : trArgs bs = some As) :
    tr (.head f bs) = some (.ordinary f As) := by simp only [tr,h,Option.map_some]

end LogicLineages.PersistentMarking.NumberedWindowSimulationHeadSupport
