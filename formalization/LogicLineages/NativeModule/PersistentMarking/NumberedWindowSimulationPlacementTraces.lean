module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationPlacementEdges
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceJoinProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementTraces
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTraceAlgebra
open NumberedWindowSimulationPlacement NumberedWindowSimulationPlacementEdges
open NumberedWindowSimulationPlacementProof (typed)
open NumberedWindowTraceTypingProof (argsStart argsEnd)

private theorem left {S K C ls rs ts} (p : Place ls rs ts) {As At Bs : NArgs}
    (leftTrace : ArgsTrace S K C ls As At) (hB : BaseTyped C Bs rs) :
    Nonempty (ArgsTrace S K C ts (weave p As Bs) (weave p At Bs)) := by
  induction leftTrace with
  | done hA => exact ⟨.done (typed p hA hB)⟩
  | raw hA hT h _ ih =>
    obtain ⟨out⟩ := ih
    exact ⟨.raw (typed p hA hB) (typed p hT hB) (rawLeft p hA hT hB h) out⟩
  | equiv h _ ih =>
    obtain ⟨out⟩ := ih
    exact ⟨.equiv (eqLeft p hB h) out⟩

private theorem right {S K C ls rs ts} (p : Place ls rs ts) {As Bs Bt : NArgs}
    (rightTrace : ArgsTrace S K C rs Bs Bt) (hA : BaseTyped C As ls) :
    Nonempty (ArgsTrace S K C ts (weave p As Bs) (weave p As Bt)) := by
  induction rightTrace with
  | done hB => exact ⟨.done (typed p hA hB)⟩
  | raw hB hT h _ ih =>
    obtain ⟨out⟩ := ih
    exact ⟨.raw (typed p hA hB) (typed p hA hT) (rawRight p hA hB hT h) out⟩
  | equiv h _ ih =>
    obtain ⟨out⟩ := ih
    exact ⟨.equiv (eqRight p hA h) out⟩

theorem both {S K C ls rs ts} (p : Place ls rs ts) {As At Bs Bt : NArgs}
    (l : ArgsTrace S K C ls As At) (r : ArgsTrace S K C rs Bs Bt) :
    Nonempty (ArgsTrace S K C ts (weave p As Bs) (weave p At Bt)) := by
  obtain ⟨leftPart⟩ := left p l (argsStart r)
  obtain ⟨rightPart⟩ := right p r (argsEnd l)
  obtain ⟨out,_⟩ := NumberedWindowTraceJoinProof.argsJoin S K C ts _ _ _ leftPart rightPart
  exact ⟨out⟩

end LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementTraces
