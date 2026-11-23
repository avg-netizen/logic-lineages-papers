module

public import LogicLineages.NativeModule.PersistentMarking.PortNormalizationTargets
public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceBasicProof

@[expose] public section

namespace LogicLineages.PersistentMarking.PortListStateProof
open Spine NameBridge DecisionSourceUniverse PortNormalization

theorem observedCons (S : Signature) (F : Inputs S) (Γ) (q : Expr) (qs : Args)
    (h : ObservedArgs F Γ (.cons q qs)) : Observed F Γ q ∧ ObservedArgs F Γ qs :=
  ⟨h 0 q .here,fun i r hr => h (i+1) r (.there hr)⟩

theorem observedRemove (S : Signature) (F : Inputs S) (Γ) {qs rest : Args} {q : Expr}
    (hr : Remove qs q rest) (h : ObservedArgs F Γ qs) : Observed F Γ q ∧ ObservedArgs F Γ rest := by
  induction hr with
  | here => exact observedCons S F Γ _ _ h
  | there hr ih =>
    obtain ⟨hx,ht⟩ := observedCons S F Γ _ _ h
    obtain ⟨hq,hr⟩ := ih ht
    refine ⟨hq,?_⟩
    intro i r ha
    cases ha with
    | here => exact hx
    | there ha => exact hr _ _ ha

theorem observedSplit (S : Signature) (F : Inputs S) (Γ) {qs left right : Args}
    (hs : Split qs left right) (h : ObservedArgs F Γ qs) :
    ObservedArgs F Γ left ∧ ObservedArgs F Γ right := by
  induction hs with
  | nil => exact ⟨(fun _ _ ha => nomatch ha),(fun _ _ ha => nomatch ha)⟩
  | left hs ih =>
    obtain ⟨hx,ht⟩ := observedCons S F Γ _ _ h
    obtain ⟨hl,hr⟩ := ih ht
    refine ⟨?_,hr⟩
    intro i r ha
    cases ha with
    | here => exact hx
    | there ha => exact hl _ _ ha
  | right hs ih =>
    obtain ⟨hx,ht⟩ := observedCons S F Γ _ _ h
    obtain ⟨hl,hr⟩ := ih ht
    refine ⟨hl,?_⟩
    intro i r ha
    cases ha with
    | here => exact hx
    | there ha => exact hr _ _ ha

theorem sourcesSplit (S : Signature) (F : Inputs S) (Γ) {qs left right : Args}
    (hs : Split qs left right) (h : Sources F Γ qs) :
    Sources F Γ left ∧ Sources F Γ right := by
  induction hs with
  | nil => exact ⟨True.intro,True.intro⟩
  | left hs ih => exact ⟨⟨h.1,(ih h.2).1⟩,(ih h.2).2⟩
  | right hs ih => exact ⟨(ih h.2).1,⟨h.1,(ih h.2).2⟩⟩
end LogicLineages.PersistentMarking.PortListStateProof
