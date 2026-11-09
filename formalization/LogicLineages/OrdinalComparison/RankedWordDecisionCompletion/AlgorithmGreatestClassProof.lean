module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmItemProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmLabelsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion Algorithm

theorem leaderClass_pair (zs : List Labelled) (label : Nat) (a : Item) :
    a ∈ leaderClass zs label ↔ (a,label) ∈ zs := by
  constructor
  · intro ha
    obtain ⟨b,hb,hfirst⟩ := List.mem_map.mp ha
    have hlabel : b.2 = label := by simpa using (List.mem_filter.mp hb).2
    cases b with
    | mk b index =>
        simp only [Prod.fst,Prod.snd] at hfirst hlabel
        subst b
        subst index
        exact (List.mem_filter.mp hb).1
  · intro ha
    exact List.mem_map.mpr ⟨(a,label),List.mem_filter.mpr ⟨ha,by simp⟩,rfl⟩

theorem foldMax_attained (xs : List Nat) (hne : xs ≠ []) : ∃ a ∈ xs, a = foldMax xs := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
      by_cases hle : foldMax xs ≤ a
      · refine ⟨a,by simp,?_⟩
        change a = max a (foldMax xs)
        exact (Nat.max_eq_left hle).symm
      · have hlt : a < foldMax xs := by omega
        have hn : xs ≠ [] := by intro hn; subst xs; simp [foldMax] at hlt
        obtain ⟨b,hb,hmax⟩ := ih hn
        refine ⟨b,by simp [hb],?_⟩
        change b = max a (foldMax xs)
        rw [Nat.max_eq_right hlt.le]
        exact hmax

/-- The last nonempty class in the runtime's increasing label enumeration
is exactly its greatest represented label. This inspects actual class lists,
not a supplied maximum-class field. -/
theorem last_nonempty_class (zs : List Labelled) (n label : Nat) (hlabel : label < n)
    (hne : leaderClass zs label ≠ []) (hall : ∀ p ∈ zs, p.2 ≤ label) :
    (((List.range n).map (leaderClass zs)).filter (fun xs => !xs.isEmpty)).getLastD [] =
      leaderClass zs label := by
  induction n generalizing label with
  | zero => omega
  | succ n ih =>
      by_cases he : label = n
      · subst label
        rw [List.range_succ,List.map_append,List.filter_append]
        have hf : ([leaderClass zs n].filter (fun xs => !xs.isEmpty)) = [leaderClass zs n] := by
          simp [hne]
        simp only [List.map_singleton,hf]
        exact List.getLastD_concat
      · have hlt : label < n := by omega
        have hnil : leaderClass zs n = [] := by
          by_contra hn
          obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ hn
          have hp := (leaderClass_pair zs n a).mp ha
          have := hall (a,n) hp
          omega
        rw [List.range_succ,List.map_append,List.filter_append]
        simpa [hnil] using ih label hlt hne hall

theorem greatest_class_data (r : Row) (labels : List Nat)
    (hlen : labels.length = (active r).length)
    (hbound : ∀ a ∈ labels, a < (active r).length) (hne : active r ≠ []) :
    ∃ label, label < (active r).length ∧ leaderClass (labelled r labels) label ≠ [] ∧
      (classes r labels).getLastD [] = leaderClass (labelled r labels) label ∧
      ∀ p ∈ labelled r labels, p.2 ≤ label := by
  have hlabels : labels ≠ [] := by
    intro hz
    have hn : (active r).length = 0 := by simp [hz] at hlen; omega
    exact hne (List.length_eq_zero_iff.mp hn)
  obtain ⟨label,hmem,hmax⟩ := foldMax_attained labels hlabels
  have hlt := hbound label hmem
  have hz : (labelled r labels).map Prod.snd = labels := List.map_snd_zip (by omega)
  have hp : label ∈ (labelled r labels).map Prod.snd := by rwa [hz]
  obtain ⟨p,hp,hplabel⟩ := List.mem_map.mp hp
  have hclass : leaderClass (labelled r labels) label ≠ [] := by
    intro he
    have hm : p.1 ∈ leaderClass (labelled r labels) label := by
      apply (leaderClass_pair _ _ _).mpr
      simpa only [← hplabel] using hp
    simp [he] at hm
  have hall : ∀ p ∈ labelled r labels, p.2 ≤ label := by
    intro q hq
    rw [hmax]
    exact member_le_foldMax labels q.2 (List.of_mem_zip hq).2
  refine ⟨label,hlt,hclass,?_,hall⟩
  exact last_nonempty_class (labelled r labels) _ label hlt hclass hall

theorem zeroClass_some_data (r : Row) (labels : List Nat) (removed : Nat)
    (h : zeroClass r labels = some removed) :
    removed < (active r).length ∧ leaderClass (labelled r labels) removed ≠ [] ∧
      leading (leaderClass (labelled r labels) removed) = 0 := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  have hr : removed < (active r).length := List.mem_range.mp hm
  have hh := Bool.and_eq_true_iff.mp hp
  exact ⟨hr,by simpa using hh.1,by simpa using hh.2⟩

theorem zeroClass_none_nonzero (r : Row) (labels : List Nat) (label : Nat)
    (hz : zeroClass r labels = none) (hlabel : label < (active r).length)
    (hne : leaderClass (labelled r labels) label ≠ []) :
    leading (leaderClass (labelled r labels) label) ≠ 0 := by
  have hnone := List.find?_eq_none.mp hz label (List.mem_range.mpr hlabel)
  intro he
  simp [hne,he] at hnone

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
