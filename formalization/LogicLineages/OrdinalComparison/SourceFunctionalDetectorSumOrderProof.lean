module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorAlgebraProof
public import Mathlib.Data.Finsupp.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof

private theorem eval_cut (f : Ordinal →₀ Ordinal) (e : Ordinal) :
    Ordinal.CNF.eval Ordinal.omega0 f = 
      Ordinal.CNF.eval Ordinal.omega0 (f.filter (fun i  => e < i)) + 
        (Ordinal.omega0 ^ e * f e + Ordinal.CNF.eval Ordinal.omega0 (f.filter (fun i  => i < e))) := by
  classical
  have hd : f = f.filter (fun i  => e < i) + (Finsupp.single e (f e) + f.filter (fun i  => i < e)) := by
    ext i
    rcases lt_trichotomy i e with hi | hi | hi
    · simp [Finsupp.filter_apply,Finsupp.single_apply,hi,hi.ne,hi.ne',not_lt_of_ge hi.le]
    · subst i; simp [Finsupp.filter_apply]
    · simp [Finsupp.filter_apply,Finsupp.single_apply,hi,hi.ne,hi.ne',not_lt_of_ge hi.le]
  conv_lhs  => rw [hd]
  rw [Ordinal.CNF.eval_add]
  · rw [Ordinal.CNF.eval_single_add]
    intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  · intro i hi j hj
    have hei : e < i := (Finset.mem_filter.mp hi).2
    have hje : j ≤ e := by
      by_contra hn
      have hej : e < j := lt_of_not_ge hn
      have hz : (Finsupp.single e (f e) + f.filter (fun k  => k < e)) j = 0 := by
        simp [Finsupp.add_apply,Finsupp.single_apply,Finsupp.filter_apply,hej.ne,hej.ne',not_lt_of_ge hej.le]
      exact (Finsupp.mem_support_iff.mp hj) hz
    exact hje.trans hei.le

private theorem eval_top_difference (f g : Ordinal →₀ Ordinal) (e : Ordinal)
    (hf : ∀ i, f i < Ordinal.omega0) (hg : ∀ i, g i < Ordinal.omega0)
    (habove : ∀ i, e < i → f i = g i) (he : f e < g e) :
    Ordinal.CNF.eval Ordinal.omega0 f < Ordinal.CNF.eval Ordinal.omega0 g := by
  classical
  have hh : f.filter (fun i  => e < i) = g.filter (fun i  => e < i) := by
    ext i
    by_cases hi : e < i
    · simp [Finsupp.filter_apply,hi,habove i hi]
    · simp [Finsupp.filter_apply,hi]
  rw [eval_cut f e,eval_cut g e,hh]
  apply add_lt_add_right
  have hlo : Ordinal.CNF.eval Ordinal.omega0 (f.filter (fun i  => i < e)) < Ordinal.omega0 ^ e := by
    apply Ordinal.CNF.eval_lt
    · intro i
      by_cases hi : i < e
      · simpa [Finsupp.filter_apply,hi] using hf i
      · simp [Finsupp.filter_apply,hi,Ordinal.omega0_pos]
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  exact (Ordinal.opow_mul_add_lt_opow_mul hlo he).trans_le le_self_add

private theorem maximal_difference (f g : Ordinal →₀ Ordinal) (hne : f ≠ g) :
    ∃ e : Ordinal, f e ≠ g e  ∧  ∀ i, e < i → f i = g i := by
  classical
  let S := (f.support ∪ g.support).filter (fun i  => f i ≠ g i)
  have hm (i : Ordinal) (hi : f i ≠ g i) : i ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,hi⟩
    by_cases hf : f i = 0
    · have hg : g i ≠ 0 := by intro hg; exact hi (hf.trans hg.symm)
      exact Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hg)
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hf)
  have hS : S.Nonempty := by
    by_contra hS
    apply hne
    ext i
    by_contra hi
    exact hS ⟨i,hm i hi⟩
  refine ⟨S.max' hS,(Finset.mem_filter.mp (Finset.max'_mem S hS)).2,?_⟩
  intro i hi
  by_contra hn
  exact (not_le_of_gt hi) (Finset.le_max' S i (hm i hn))

theorem sum_strict_right (a b c : Ordinal) (hab : a < b) :
    ordinalNaturalSum a c < ordinalNaturalSum b c := by
  classical
  let f := Ordinal.CNF.coeff Ordinal.omega0 a
  let g := Ordinal.CNF.coeff Ordinal.omega0 b
  let k := Ordinal.CNF.coeff Ordinal.omega0 c
  have hne : f ≠ g := by
    intro he
    have ha := congrArg (Ordinal.CNF.eval Ordinal.omega0) he
    simp only [f,g,Ordinal.CNF.eval_coeff] at ha
    exact (ne_of_lt hab) ha
  obtain ⟨e,he,higher⟩ := maximal_difference f g hne
  have hlt : f e < g e := by
    rcases lt_or_gt_of_ne he with h | h
    · exact h
    · have hr := eval_top_difference g f e (coeff_finite b) (coeff_finite a)
        (fun i hi  => (higher i hi).symm) h
      simp only [f,g,Ordinal.CNF.eval_coeff] at hr
      exact False.elim (lt_asymm hab hr)
  unfold ordinalNaturalSum
  apply eval_top_difference (f + k) (g + k) e
  · intro i
    exact Ordinal.isPrincipal_add_omega0 (coeff_finite a i) (coeff_finite c i)
  · intro i
    exact Ordinal.isPrincipal_add_omega0 (coeff_finite b i) (coeff_finite c i)
  · intro i hi
    simp only [Finsupp.add_apply,higher i hi]
  · obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
    obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
    obtain ⟨v,hv⟩ := Ordinal.lt_omega0.mp (coeff_finite c e)
    change (Ordinal.CNF.coeff Ordinal.omega0 a e) < (Ordinal.CNF.coeff Ordinal.omega0 b e) at hlt
    rw [hm,hn] at hlt
    have hmn : m < n := by exact_mod_cast hlt
    change Ordinal.CNF.coeff Ordinal.omega0 a e + Ordinal.CNF.coeff Ordinal.omega0 c e < 
      Ordinal.CNF.coeff Ordinal.omega0 b e + Ordinal.CNF.coeff Ordinal.omega0 c e
    rw [hm,hn,hv]
    exact_mod_cast Nat.add_lt_add_right hmn v

theorem sum_strict_left (a b c : Ordinal) (hab : a < b) :
    ordinalNaturalSum c a < ordinalNaturalSum c b := by
  rw [sum_comm c a,sum_comm c b]
  exact sum_strict_right a b c hab
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
