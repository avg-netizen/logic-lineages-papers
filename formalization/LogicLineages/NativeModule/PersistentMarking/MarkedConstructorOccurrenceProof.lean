module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorOccurrenceProof
open Spine NameBridge DecisionPorts HereditaryDomainCode MarkedConstructorTargets

theorem removalSound {ts : List Expr} {t : Expr} {rest : List Expr}
    (h : (t,rest) ∈ MarkedConstructorTests.removals ts) : Delete t ts rest := by
  induction ts generalizing rest with
  | nil => simp [MarkedConstructorTests.removals] at h
  | cons q qs ih =>
    simp only [MarkedConstructorTests.removals,List.mem_cons,List.mem_map] at h
    rcases h with h | ⟨p,hp,he⟩
    · cases h; exact .here
    · cases he
      exact .there (ih hp)

theorem removalComplete {ts : List Expr} {t : Expr} {rest : List Expr}
    (h : Delete t ts rest) : (t,rest) ∈ MarkedConstructorTests.removals ts := by
  induction h with
  | here => exact List.mem_cons_self
  | there h ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,ih,rfl⟩)

theorem splitSound {α : Type} {xs ys zs : List α}
    (h : (ys,zs) ∈ MarkedConstructorTests.splits xs) : SplitList xs ys zs := by
  induction xs generalizing ys zs with
  | nil => simp only [MarkedConstructorTests.splits,List.mem_singleton] at h; cases h; exact .nil
  | cons x xs ih =>
    simp only [MarkedConstructorTests.splits,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at h
    obtain ⟨p,hp,he⟩ := h
    rcases he with he | he
    · cases he; exact .left (ih hp)
    · cases he; exact .right (ih hp)

theorem splitComplete {α : Type} {xs ys zs : List α}
    (h : SplitList xs ys zs) : (ys,zs) ∈ MarkedConstructorTests.splits xs := by
  induction h with
  | nil => exact List.mem_cons_self
  | left h ih =>
    exact List.mem_flatMap.mpr ⟨_,ih,List.mem_cons_self⟩
  | right h ih =>
    exact List.mem_flatMap.mpr ⟨_,ih,List.mem_cons_of_mem _ (List.mem_cons_self)⟩

theorem matching : MarkedConstructorTargets.MatchingExact := by
  intro E Γ bs
  induction bs with
  | nil =>
    intro ts
    constructor
    · intro h
      have ht : ts = [] := by simpa [MarkedConstructorTests.matching] using h
      subst ts; exact .nil
    · intro h; cases h; rfl
  | cons a bs ih =>
    intro ts
    constructor
    · intro h
      obtain ⟨p,hp,hbit,hmatch⟩ := (by
        simpa only [MarkedConstructorTests.matching,List.any_eq_true,Bool.and_eq_true] using h :
        ∃ p, p ∈ MarkedConstructorTests.removals ts ∧
          MarkedConstructorTests.bit false E Γ a p.1 = true ∧ MarkedConstructorTests.matching E Γ bs p.2 = true)
      exact .cons (removalSound hp) hbit ((ih p.2).mp hmatch)
    · intro h
      cases h with
      | cons hd hb hm =>
        simp only [MarkedConstructorTests.matching,List.any_eq_true,Bool.and_eq_true]
        exact ⟨_,removalComplete hd,hb,(ih _).mpr hm⟩

theorem multiset : MarkedConstructorTargets.MultisetExact := by
  intro E Γ bs ts
  simp only [MarkedConstructorTests.multiset,List.any_eq_true,Bool.and_eq_true,
    MarkedConstructorTests.coverage,List.all_eq_true]
  constructor
  · rintro ⟨source,hs,hn,target,ht,hm,hc⟩
    refine ⟨source.1,source.2,target.1,target.2,splitSound hs,splitSound ht,?_,
      (matching E Γ _ _).mp hm,hc⟩
    simpa using hn
  · rintro ⟨kept,removed,matched,added,hs,ht,hn,hm,hc⟩
    refine ⟨(kept,removed),splitComplete hs,?_,(matched,added),splitComplete ht,
      (matching E Γ _ _).mpr hm,hc⟩
    simpa using hn
end LogicLineages.PersistentMarking.MarkedConstructorOccurrenceProof
