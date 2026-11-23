module

public import LogicLineages.NativeModule.PersistentMarking.PortListStateProof
public import LogicLineages.NativeModule.PersistentMarking.PortStateProof
public import LogicLineages.NativeModule.PersistentMarking.ExtendedRenameSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.PortListCasesProof
open Spine NameBridge PortNormalization RefinementRenamingTargets RefinementRenameSupport

theorem matchingCons (S : Signature) (F : Inputs S) (targets : Args) (x y : Expr) (xs rest : Args)
    (hr : Remove targets y rest) (ihw : WeakMotive F x y) (ihm : MatchingMotive F xs rest) :
    MatchingMotive F (.cons x xs) targets := by
  intro π Γ hp hw hu ho
  have hr' := ExtendedRenameSupport.remove π hr
  obtain ⟨hy,hrest⟩ := PortListStateProof.observedRemove S F Γ hr' ho
  exact .cons hr' (ihw π Γ hp hw hu.1 hy) (ihm π Γ hp hw hu.2 hrest)

theorem multisetReplace (S : Signature) (F : Inputs S) (source kept removed target matched added : Args)
    (hs : Split source kept removed) (ht : Split target matched added) (hn : Nonempty removed)
    (ihm : MatchingMotive F kept matched) (ihc : CoverageMotive F removed added) :
    MultisetMotive F source target := by
  intro π Γ hp hw hu ho
  have hs' := ExtendedRenameSupport.mapSplit π hs
  have ht' := ExtendedRenameSupport.mapSplit π ht
  obtain ⟨hk,hr⟩ := PortListStateProof.sourcesSplit S F Γ hs' hu
  obtain ⟨hm,ha⟩ := PortListStateProof.observedSplit S F Γ ht' ho
  exact .replace hs' ht' (ExtendedRenameSupport.nonempty π removed hn)
    (ihm π Γ hp hw hk hm) (ihc π Γ hp hw hr ha)

theorem coverageCons (S : Signature) (F : Inputs S) (owners : Args) (i : Nat) (q x : Expr) (xs : Args)
    (ha : At owners i q) (ihs : StrictMotive F q x) (ihc : CoverageMotive F owners xs) :
    CoverageMotive F owners (.cons x xs) := by
  intro π Γ hp hw hu ho
  have ha' := mapAt π ha
  obtain ⟨hx,hxs⟩ := PortListStateProof.observedCons S F Γ _ _ ho
  exact .cons ha' (ihs π Γ hp hw (DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _ hu ha') hx)
    (ihc π Γ hp hw hu hxs)

theorem wholeCons (S : Signature) (F : Inputs S) (f : Head) (bs es : Args) (q : Expr) (qs : Args)
    (ihw : WeakMotive F (.marked f q.type bs es) q) (ihs : WholeMotive F f bs es qs) :
    WholeMotive F f bs es (.cons q qs) := by
  intro π Γ hp hw hu ho
  obtain ⟨hq,hqs⟩ := PortListStateProof.observedCons S F Γ _ _ ho
  have hqu := PortStateProof.observedUniverse S F Γ _ hw hq
  have hqK := DecisionSourceBasicProof.rootType _ _ _ _ _ hqu
  have hsource := hu (rename π q).type hqK
  rw [renameType] at hsource
  have hchild := ihw π Γ hp hw hsource hq
  rw [← renameType π q] at hchild
  exact .cons hchild (ihs π Γ hp hw hu hqs)
end LogicLineages.PersistentMarking.PortListCasesProof
