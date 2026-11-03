module
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsTargets
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.OfFn
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeGuards.Proof
open CommonHeadCollectedRow

theorem conjunction_eval (ps : List Formula) (ν : Nat → Nat) :
    (conjunction ps).eval ν ↔ ∀ p∈ps, p.eval ν := by
  induction ps with
  | nil => simp [conjunction,Formula.eval]
  | cons p ps ih => simpa [conjunction,Formula.eval] using and_congr Iff.rfl ih

theorem disjunction_eval (ps : List Formula) (ν : Nat → Nat) :
    (disjunction ps).eval ν ↔ ∃ p∈ps, p.eval ν := by
  induction ps with
  | nil => simp [disjunction,Formula.eval]
  | cons p ps ih => simpa [disjunction,Formula.eval] using or_congr Iff.rfl ih

private theorem masks_mem (n : Nat) (mask : List Bool) : mask∈masks n ↔ mask.length=n := by
  induction n generalizing mask with
  | zero => cases mask <;> simp [masks]
  | succ n ih =>
    cases mask with
    | nil => simp [masks]
    | cons b bs => cases b <;> simp [masks,ih]

private theorem maskGuard_eval (m i : Nat) (mask : List Bool) (ν : Nat → Nat) :
    (maskGuard m i mask).eval ν ↔ ∀ j<m, mask.getD j false=decide (ν i=ν j) := by
  rw [maskGuard,conjunction_eval]
  simp only [List.forall_mem_map,List.mem_range]
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro hj
  cases hb : mask.getD j false <;> simp [hb,Formula.eval]

private theorem coefficient_mask (cs : List Int) (mask : List Bool) (i : Nat) (ν : Nat → Nat)
    (hlen : mask.length=cs.length)
    (hmask : ∀ j<cs.length, mask.getD j false=decide (ν i=ν j)) :
    maskCoefficient cs mask=coefficient (inputRow cs ν) (ν i) := by
  unfold maskCoefficient coefficient inputRow
  apply congrArg List.sum
  simp only [List.map_map,Function.comp_def]
  apply List.ext_getElem
  · simp [hlen]
  · intro j hj hk
    have hjc : j<cs.length := by simpa [hlen] using hj
    have hjm : j<mask.length := by omega
    have hm := hmask j hjc
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hjm,Option.getD_some] at hm
    simp only [List.getElem_zipWith,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    rw [hm]
    by_cases he : ν i=ν j
    · simp [he]
    · simp [he,Ne.symm he]

theorem exactBlockFormula : Targets.ExactBlockFormula := by
  intro cs i desired ν
  rw [blockFormula,disjunction_eval]
  constructor
  · rintro ⟨p,hp,hg⟩
    obtain ⟨mask,hm,rfl⟩ := List.mem_map.mp hp
    obtain ⟨hm,hs⟩ := List.mem_filter.mp hm
    have hs : Int.sign (maskCoefficient cs mask)=desired := of_decide_eq_true hs
    rw [coefficient_mask cs mask i ν ((masks_mem _ _).mp hm) ((maskGuard_eval _ _ _ _).mp hg)] at hs
    exact hs
  · intro hs
    let mask := List.ofFn (fun j : Fin cs.length => decide (ν i=ν j.val))
    have hlen : mask.length=cs.length := List.length_ofFn
    have hm : ∀ j<cs.length, mask.getD j false=decide (ν i=ν j) := by
      intro j hj
      simp [mask,List.getD_eq_getElem?_getD,hj]
    refine ⟨maskGuard cs.length i mask, List.mem_map.mpr ⟨mask,?_,rfl⟩,
      (maskGuard_eval _ _ _ _).mpr hm⟩
    apply List.mem_filter.mpr
    refine ⟨(masks_mem _ _).mpr hlen,?_⟩
    apply decide_eq_true

    rw [coefficient_mask cs mask i ν hlen hm]
    exact hs

private def Supported (m : Nat) (p : Formula) := ∀ j∈p.variables, j<m
private theorem conj_support {m : Nat} {p q : Formula} (hp : Supported m p) (hq : Supported m q) :
    Supported m (.conj p q) := by
  intro j hj
  rcases List.mem_append.mp hj with h | h
  · exact hp j h
  · exact hq j h
private theorem disj_support {m : Nat} {p q : Formula} (hp : Supported m p) (hq : Supported m q) :
    Supported m (.disj p q) := conj_support hp hq
private theorem conjunction_support (m : Nat) (ps : List Formula)
    (h : ∀ p∈ps, Supported m p) : Supported m (conjunction ps) := by
  induction ps with
  | nil => simp [Supported,conjunction,Formula.variables]
  | cons p ps ih => exact conj_support (h p List.mem_cons_self) (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))
private theorem disjunction_support (m : Nat) (ps : List Formula)
    (h : ∀ p∈ps, Supported m p) : Supported m (disjunction ps) := by
  induction ps with
  | nil => simp [Supported,disjunction,Formula.variables]
  | cons p ps ih => exact disj_support (h p List.mem_cons_self) (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))
private theorem eq_support {m i j : Nat} (hi : i<m) (hj : j<m) : Supported m (.eq i j) := by
  simpa [Supported,Formula.variables] using And.intro hi hj
private theorem mask_support (m i : Nat) (mask : List Bool) (hi : i<m) : Supported m (maskGuard m i mask) := by
  apply conjunction_support
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  have hj' := List.mem_range.mp hj
  split <;> exact eq_support hi hj'
private theorem block_support (cs : List Int) (i : Nat) (desired : Int) (hi : i<cs.length) :
    Supported cs.length (blockFormula cs i desired) := by
  apply disjunction_support
  intro p hp
  obtain ⟨mask,hm,rfl⟩ := List.mem_map.mp hp
  exact mask_support cs.length i mask hi
private theorem canceled_support (cs : List Int) : Supported cs.length (canceledFormula cs) := by
  apply conjunction_support
  intro p hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact block_support cs i 0 (List.mem_range.mp hi)
private theorem maximal_support (cs : List Int) (i : Nat) (hi : i<cs.length) :
    Supported cs.length (maximalFormula cs i) := by
  apply conjunction_support
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  apply disj_support
  · exact eq_support hi (List.mem_range.mp hj)
  · exact block_support cs j 0 (List.mem_range.mp hj)

theorem originalInputSupport : Targets.OriginalInputSupport := by
  intro K cs desired
  change Supported cs.length (largeFormula K cs desired)
  apply conj_support
  · apply conjunction_support
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    simpa [Supported,Formula.variables] using List.mem_range.mp hi
  · apply disj_support
    · apply conj_support
      · split <;> simp [Supported,Formula.variables]
      · exact canceled_support cs
    · split
      · simp [Supported,Formula.variables]
      · apply disjunction_support
        intro p hp
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
        exact conj_support (block_support cs i desired (List.mem_range.mp hi))
          (maximal_support cs i (List.mem_range.mp hi))
end LogicLineages.OrdinalComparison.CommonHeadLargeGuards.Proof
