module
public import LogicLineages.StandardControlCurrent.MixedCancellationSemanticProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellation
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

private theorem select_predicate (xs : List (Int × Summand))
    (p : Int × Summand → Bool) :
    ((xs.zip (xs.map p)).filterMap (fun a => if a.2 then some a.1 else none)) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons,List.zip_cons_cons,List.filterMap_cons,List.filter_cons]
      cases h : p a <;> simp [h,ih]

theorem classCoverage : MixedCancellationTargets.ClassCoverage := by
  intro r anchor ha ν
  let p : Int × Summand → Bool := fun a => decide (a.2.term.value ν = anchor.2.term.value ν)
  let bs := r.2.map p
  have he : selected r bs = r.2.filter p := select_predicate r.2 p
  have hm : anchor ∈ selected r bs := by
    rw [he]
    simp [p,ha]
  refine ⟨bs,(enumeration _ _).mpr (by simp [bs]),he,hm,?_⟩
  have hv : ∀ a ∈ selected r bs, a.2.term.value ν = anchor.2.term.value ν := by
    intro a h
    rw [he] at h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  cases hs : selected r bs with
  | nil => simp [equalGuard,hs,Matrix.eval]
  | cons a as =>
      have hav := hv a (by simp [hs])
      simp only [equalGuard,hs]
      change (OrderedOccurrence.all (as.map fun b => Matrix.equal b.2.term a.2.term)).eval ν
      apply (OrderedOccurrenceProof.all_eval _ _).mpr
      intro q hq
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
      exact (hv b (by simp [hs,hb])).trans hav.symm
end LogicLineages.StandardControlCurrent.MixedCancellation
