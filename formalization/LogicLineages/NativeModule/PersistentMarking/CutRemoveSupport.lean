module

public import LogicLineages.NativeModule.PersistentMarking.CutOccurrenceTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.CutRemoveSupport
open Spine ExtendedMeasure

theorem removeSwap {xs rest final : Args} {a b : Expr}
    (ha : Remove xs a rest) (hb : Remove rest b final) :
    ∃ mid, Remove xs b mid ∧ Remove mid a final := by
  induction ha generalizing final with
  | here => exact ⟨.cons _ final,.there hb,.here⟩
  | there ha ih =>
    cases hb with
    | here => exact ⟨_,.here,ha⟩
    | there hb =>
      obtain ⟨mid,hm,hn⟩ := ih hb
      exact ⟨.cons _ mid,.there hm,.there hn⟩

theorem removeOrdinaryParts {xs rest : Args} {x : Expr} (h : Remove xs x rest)
    (ho : OrdinaryArgs xs) : Ordinary x ∧ OrdinaryArgs rest := by
  induction h with
  | here => exact ho
  | there hr ih =>
    have hh := ih ho.2
    exact ⟨hh.1,ho.1,hh.2⟩

end LogicLineages.PersistentMarking.CutRemoveSupport
