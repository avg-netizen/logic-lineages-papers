module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathSupportProof
open DirectMultisetCutPath

theorem dominatedMultisetPath {α : Type} (R : α → α → Prop) (removed : List α) :
    ∀ kept inserted : Multiset α, (∀ y ∈ inserted, ∃ a ∈ removed, R a y) →
      CutPath R removed.length (kept + (removed : Multiset α)) (kept + inserted) := by
  classical
  induction removed with
  | nil =>
    intro kept inserted h
    have hz : inserted = 0 := Multiset.eq_zero_of_forall_notMem (by
      intro y hy
      obtain ⟨a, ha, _⟩ := h y hy
      simp at ha)
    subst inserted
    simpa using CutPath.refl (R := R) kept
  | cons a rest ih =>
    intro kept inserted h
    let bucket := inserted.filter (R a)
    let remaining := inserted.filter (fun y => ¬ R a y)
    have hsplit : bucket + remaining = inserted := Multiset.filter_add_not (R a) inserted
    have hremaining : ∀ y ∈ remaining, ∃ b ∈ rest, R b y := by
      intro y hy
      obtain ⟨hy, hnot⟩ := Multiset.mem_filter.mp hy
      obtain ⟨b, hb, hr⟩ := h y hy
      rcases List.mem_cons.mp hb with rfl | hb
      · exact False.elim (hnot hr)
      · exact ⟨b, hb, hr⟩
    have hcut : Relation.CutExpand (fun successor source => R source successor)
        ((kept + bucket) + (rest : Multiset α))
        (kept + ((a :: rest : List α) : Multiset α)) := by
      refine ⟨bucket, a, ?_, ?_⟩
      · intro y hy
        exact (Multiset.mem_filter.mp hy).2
      · simp [← Multiset.cons_coe, ← Multiset.singleton_add, add_assoc, add_comm, add_left_comm]
    have htail := ih (kept + bucket) remaining hremaining
    have hpath := CutPath.cons hcut htail
    simpa only [List.length_cons, add_assoc, hsplit] using hpath

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetCutPathSupportProof
