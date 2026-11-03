module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsTargets
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsMaskProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Proof
open CommonHeadLargeGuards (Formula conjunction disjunction masks maskCoefficient)
open CommonHeadLargeGuards.Proof (conjunction_eval disjunction_eval)

theorem head_repr_eq_iff (a b : NONote) : a.1.repr = b.1.repr ↔ a = b := by
  constructor
  · intro h
    exact Subtype.ext (ONote.repr_inj.mp h)
  · intro h
    cases h
    rfl

theorem key_equal_eval (heads : Nat → NONote) (i j : Nat) (ν : Nat → Nat) :
    (keyEqualFormula heads i j).eval ν ↔
      (heads i).1.repr = (heads j).1.repr ∧ ν i = ν j := by
  classical
  rw [head_repr_eq_iff]
  by_cases h : heads i = heads j <;> simp [keyEqualFormula, h, Formula.eval]

theorem key_less_eval (heads : Nat → NONote) (i j : Nat) (ν : Nat → Nat) :
    (keyLessFormula heads i j).eval ν ↔
      actualHeadKeyLess (heads i).1.repr (ν i) (heads j).1.repr (ν j) := by
  classical
  unfold actualHeadKeyLess
  rw [head_repr_eq_iff]
  by_cases hl : (heads i).1.repr < (heads j).1.repr
  · simp [keyLessFormula, hl, Formula.eval]
  · by_cases he : heads i = heads j <;>
      simp [keyLessFormula, hl, he, Formula.eval]

private theorem masks_mem (n : Nat) (mask : List Bool) :
    mask ∈ masks n ↔ mask.length = n := by
  induction n generalizing mask with
  | zero => cases mask <;> simp [masks]
  | succ n ih =>
    cases mask with
    | nil => simp [masks]
    | cons b bs => cases b <;> simp [masks, ih]

private theorem maskGuard_eval (heads : Nat → NONote) (m i : Nat)
    (mask : List Bool) (ν : Nat → Nat) :
    (maskGuard heads m i mask).eval ν ↔
      ∀ j < m, mask.getD j false = decide (heads i = heads j ∧ ν i = ν j) := by
  classical
  rw [maskGuard, conjunction_eval]
  simp only [List.forall_mem_map, List.mem_range]
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro hj
  cases hb : mask.getD j false <;>
    simp [hb, Formula.eval, key_equal_eval, head_repr_eq_iff]

private theorem coefficient_mask (heads : Nat → NONote) (cs : List Int)
    (mask : List Bool) (i : Nat) (ν : Nat → Nat)
    (hlen : mask.length = cs.length)
    (hmask : ∀ j < cs.length,
      mask.getD j false = decide (heads i = heads j ∧ ν i = ν j)) :
    maskCoefficient cs mask = blockCoefficient heads cs ν i := by
  classical
  unfold maskCoefficient blockCoefficient
  apply congrArg List.sum
  apply List.ext_getElem
  · simp [hlen]
  · intro j hj hk
    have hjc : j < cs.length := by simpa [hlen] using hj
    have hjm : j < mask.length := by omega
    have hm := hmask j hjc
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjm,
      Option.getD_some] at hm
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_zipIdx,
      Nat.zero_add]
    rw [hm]
    simp only [decide_eq_true_eq]
    have he : (heads i = heads j ∧ ν i = ν j) ↔
        (heads j = heads i ∧ ν j = ν i) := by
      constructor <;> rintro ⟨hh, hv⟩ <;> exact ⟨hh.symm, hv.symm⟩
    by_cases h : heads i = heads j ∧ ν i = ν j
    · rw [if_pos h, if_pos (he.mp h)]
    · rw [if_neg h, if_neg (fun hr => h (he.mpr hr))]

theorem block_eval (heads : Nat → NONote) (cs : List Int) (i : Nat)
    (desired : Int) (ν : Nat → Nat) :
    (blockFormula heads cs i desired).eval ν ↔
      Int.sign (blockCoefficient heads cs ν i) = desired := by
  classical
  rw [blockFormula, disjunction_eval]
  constructor
  · rintro ⟨p, hp, hg⟩
    obtain ⟨mask, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hm, hs⟩ := List.mem_filter.mp hm
    have hs : Int.sign (maskCoefficient cs mask) = desired := of_decide_eq_true hs
    rw [coefficient_mask heads cs mask i ν ((masks_mem _ _).mp hm)
      ((maskGuard_eval _ _ _ _ _).mp hg)] at hs
    exact hs
  · intro hs
    let mask := List.ofFn (fun j : Fin cs.length =>
      decide (heads i = heads j.val ∧ ν i = ν j.val))
    have hlen : mask.length = cs.length := List.length_ofFn
    have hm : ∀ j < cs.length,
        mask.getD j false = decide (heads i = heads j ∧ ν i = ν j) := by
      intro j hj
      simp [mask, List.getD_eq_getElem?_getD, hj]
    refine ⟨maskGuard heads cs.length i mask,
      List.mem_map.mpr ⟨mask, ?_, rfl⟩,
      (maskGuard_eval _ _ _ _ _).mpr hm⟩
    apply List.mem_filter.mpr
    refine ⟨(masks_mem _ _).mpr hlen, ?_⟩
    apply decide_eq_true
    rw [coefficient_mask heads cs mask i ν hlen hm]
    exact hs

theorem exactHeadAwareBlocks : Targets.ExactHeadAwareBlocks := by
  intro heads ν
  exact ⟨fun i j => key_equal_eval heads i j ν,
    fun i j => key_less_eval heads i j ν,
    fun cs i desired => block_eval heads cs i desired ν⟩

private def Supported (m : Nat) (p : Formula) : Prop :=
  ∀ j ∈ p.variables, j < m

private theorem conj_support {m : Nat} {p q : Formula}
    (hp : Supported m p) (hq : Supported m q) : Supported m (.conj p q) := by
  intro j hj
  rcases List.mem_append.mp hj with h | h
  · exact hp j h
  · exact hq j h

private theorem disj_support {m : Nat} {p q : Formula}
    (hp : Supported m p) (hq : Supported m q) : Supported m (.disj p q) :=
  conj_support hp hq

private theorem conjunction_support (m : Nat) (ps : List Formula)
    (h : ∀ p ∈ ps, Supported m p) : Supported m (conjunction ps) := by
  induction ps with
  | nil => simp [Supported, conjunction, Formula.variables]
  | cons p ps ih =>
    exact conj_support (h p List.mem_cons_self)
      (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

private theorem disjunction_support (m : Nat) (ps : List Formula)
    (h : ∀ p ∈ ps, Supported m p) : Supported m (disjunction ps) := by
  induction ps with
  | nil => simp [Supported, disjunction, Formula.variables]
  | cons p ps ih =>
    exact disj_support (h p List.mem_cons_self)
      (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

private theorem key_equal_support {m i j : Nat} (heads : Nat → NONote)
    (hi : i < m) (hj : j < m) : Supported m (keyEqualFormula heads i j) := by
  classical
  unfold keyEqualFormula
  split <;> simp [Supported, Formula.variables, hi, hj]

private theorem key_less_support {m i j : Nat} (heads : Nat → NONote)
    (hi : i < m) (hj : j < m) : Supported m (keyLessFormula heads i j) := by
  classical
  unfold keyLessFormula
  split_ifs <;> simp [Supported, Formula.variables, hi, hj]

private theorem mask_support {n : Nat} (heads : Nat → NONote)
    (m i : Nat) (mask : List Bool) (hm : m ≤ n) (hi : i < n) :
    Supported n (maskGuard heads m i mask) := by
  apply conjunction_support
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have hj' : j < n := (List.mem_range.mp hj).trans_le hm
  split <;> exact key_equal_support heads hi hj'

private theorem block_support {n : Nat} (heads : Nat → NONote)
    (cs : List Int) (i : Nat) (desired : Int)
    (hc : cs.length ≤ n) (hi : i < n) :
    Supported n (blockFormula heads cs i desired) := by
  apply disjunction_support
  intro p hp
  obtain ⟨mask, hm, rfl⟩ := List.mem_map.mp hp
  exact mask_support heads cs.length i mask hc hi

private theorem canceled_support {n : Nat} (heads : Nat → NONote)
    (cs : List Int) (hc : cs.length ≤ n) :
    Supported n (canceledFormula heads cs) := by
  apply conjunction_support
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact block_support heads cs i 0 hc ((List.mem_range.mp hi).trans_le hc)

private theorem maximal_support {n : Nat} (heads : Nat → NONote)
    (cs : List Int) (i : Nat) (hc : cs.length ≤ n) (hi : i < n) :
    Supported n (maximalFormula heads cs i) := by
  apply conjunction_support
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have hj' : j < n := (List.mem_range.mp hj).trans_le hc
  exact disj_support (key_less_support heads hi hj')
    (block_support heads cs j 0 hc hj')

private theorem difference_support {m left right : Nat} (desired : Int)
    (hl : left < m) (hr : right < m) :
    Supported m (differenceSignFormula left right desired) := by
  unfold differenceSignFormula
  split_ifs <;> simp [Supported, Formula.variables, hl, hr]

theorem largeFormula_label_bound (L : Nat) (heads : Nat → NONote)
    (cs : List Int) (desired : Int) :
    ∀ i ∈ (largeFormula L heads cs desired).variables, i < cs.length + 2 := by
  change Supported (cs.length + 2) (largeFormula L heads cs desired)
  have hc : cs.length ≤ cs.length + 2 := by omega
  apply conj_support
  · apply conjunction_support
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hi' : i < cs.length + 2 := (List.mem_range.mp hi).trans_le hc
    simpa [Supported, Formula.variables] using hi'
  · apply disj_support
    · exact conj_support (canceled_support heads cs hc)
        (difference_support desired (by omega) (by omega))
    · split
      · simp [Supported, Formula.variables]
      · apply disjunction_support
        intro p hp
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        have hi' : i < cs.length + 2 := (List.mem_range.mp hi).trans_le hc
        exact conj_support (block_support heads cs i desired hc hi')
          (maximal_support heads cs i hc hi')

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Proof
