module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceTargets
public import Mathlib.Data.List.Enum
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence

theorem exactRoster : OrderedOccurrenceTargets.ExactRoster := by
  intro p r j c s
  constructor
  · intro hm
    obtain ⟨⟨row,ri⟩,hr,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨⟨⟨cc,ss⟩,ji⟩,hi,he⟩ := List.mem_map.mp hm
    cases he
    exact ⟨row,List.mk_mem_zipIdx_iff_getElem?.mp hr,List.mk_mem_zipIdx_iff_getElem?.mp hi⟩
  · rintro ⟨row,hr,hi⟩
    apply List.mem_flatMap.mpr
    refine ⟨(row,r),List.mk_mem_zipIdx_iff_getElem?.mpr hr,?_⟩
    exact List.mem_map.mpr ⟨((c,s),j),List.mk_mem_zipIdx_iff_getElem?.mpr hi,rfl⟩

theorem exactLive : OrderedOccurrenceTargets.ExactLive := by
  intro xs p o
  simp only [live,List.mem_filter,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq]
  tauto

theorem exactInactive : OrderedOccurrenceTargets.ExactInactive := by
  intro xs p i
  simp only [inactive, List.mem_filter, Bool.not_eq_true, List.any_eq_false, beq_eq_false_iff_ne]

theorem all_eval (ps : List Matrix) (ν : Nat → Nat) :
    (OrderedOccurrence.all ps).eval ν ↔ ∀ p ∈ ps, p.eval ν := by
  induction ps with
  | nil => simp [OrderedOccurrence.all,Matrix.eval]
  | cons p ps ih => simp [OrderedOccurrence.all,Matrix.eval,ih]

private theorem finite_max {α : Type} (f : α → Nat) (xs : List α) (hne : xs ≠ []) :
    ∃ a ∈ xs, ∀ b ∈ xs, f b ≤ f a := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons a xs ih =>
    by_cases he : xs=[]
    · subst xs
      refine ⟨a,by simp,?_⟩
      intro b hb
      have he : b=a := List.mem_singleton.mp hb
      subst b
      exact Nat.le_refl _
    · obtain ⟨b,hb,hmax⟩ := ih he
      by_cases hab : f a ≤ f b
      · refine ⟨b,List.mem_cons_of_mem a hb,?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact hmax c hc
      · refine ⟨a,List.mem_cons_self,?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Nat.le_refl _
        · exact (hmax c hc).trans (by omega)

theorem maximumCoverage : OrderedOccurrenceTargets.MaximumCoverage := by
  intro xs p hne ν
  obtain ⟨o,ho,hm⟩ := finite_max (fun a => (summand a).term.value ν) (live xs p) hne
  refine ⟨o,ho,?_⟩
  rw [maximal,all_eval]
  intro q hq
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
  exact Nat.not_lt.mpr (hm a ha)
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
