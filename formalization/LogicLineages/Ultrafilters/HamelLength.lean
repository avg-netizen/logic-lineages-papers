module

public import LogicLineages.Ultrafilters.HamelTargets
public import LogicLineages.Ultrafilters.Translation
public import Mathlib.Order.Filter.Finite
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem supportLength_eq_zero {ι : Type*} (B : Module.Basis ι ℚ ℝ) (x : ℝ) :
    supportLength B x = 0 ↔ x = 0 := by
  simp only [supportLength, Finset.card_eq_zero, Finsupp.support_eq_empty]
  constructor
  · intro h
    apply B.repr.injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero B.repr

theorem coordinateKernel_mem {ι : Type*} (B : Module.Basis ι ℚ ℝ)
    (p : Ultrafilter ℝ) (hz : ∀ i, {x | B.repr x i = 0} ∈ p) (x : ℝ) :
    coordinateKernel B x ∈ p := by
  have hi : (⋂ i ∈ (B.repr x).support, {y | B.repr y i = 0}) ∈ p :=
    (Filter.biInter_finset_mem _).mpr (fun i _ => hz i)
  simpa only [Set.mem_iInter, coordinateKernel, Set.setOf_forall] using hi

theorem supportLength_add_of_kernel {ι : Type*} (B : Module.Basis ι ℚ ℝ)
    (x y : ℝ) (hy : y ∈ coordinateKernel B x) :
    supportLength B (x + y) = supportLength B x + supportLength B y := by
  classical
  have hd : Disjoint (B.repr x).support (B.repr y).support := by
    apply Finset.disjoint_left.mpr
    intro i hx hi
    exact (Finsupp.mem_support_iff.mp hi) (hy i hx)
  simp only [supportLength, map_add, Finsupp.support_add_eq hd,
    Finset.card_union_of_disjoint hd]

theorem hamel_length_escapes : Targets.HamelLengthEscapes := by
  intro ι B p hp hz
  have hlevels : ∀ k : Nat, {x | supportLength B x = k} ∉ p := by
    intro k hk
    by_cases hkzero : k = 0
    · obtain ⟨x, hx, hpos⟩ := Filter.nonempty_of_mem
        (Filter.inter_mem hk (hp.2 1 zero_lt_one))
      have hxzero : x = 0 := (supportLength_eq_zero B x).mp (hx.trans hkzero)
      exact (ne_of_gt hpos.1) hxzero
    · have hdouble : {x | supportLength B x = k + k} ∈ p := by
        apply (hp.1 {x | supportLength B x = k + k}).mpr
        apply Filter.mem_of_superset hk
        intro x hx
        apply Filter.mem_of_superset (Filter.inter_mem (coordinateKernel_mem B p hz x) hk)
        intro y hy
        change supportLength B (x + y) = k + k
        rw [supportLength_add_of_kernel B x y hy.1, hx, hy.2]
      obtain ⟨x, hx, hxdouble⟩ := Filter.nonempty_of_mem (Filter.inter_mem hk hdouble)
      have heq : k = k + k := hx.symm.trans hxdouble
      omega
  refine ⟨hlevels, ?_⟩
  intro m
  induction m with
  | zero =>
    have hc := Ultrafilter.compl_mem_iff_notMem.mpr (hlevels 0)
    apply Filter.mem_of_superset hc
    intro x hx
    change supportLength B x ≠ 0 at hx
    change 0 < supportLength B x
    omega
  | succ m ih =>
    have hc := Ultrafilter.compl_mem_iff_notMem.mpr (hlevels (m + 1))
    apply Filter.mem_of_superset (Filter.inter_mem ih hc)
    intro x hx
    change m < supportLength B x ∧ supportLength B x ≠ m + 1 at hx
    change m + 1 < supportLength B x
    omega

end LogicLineages.Ultrafilters
