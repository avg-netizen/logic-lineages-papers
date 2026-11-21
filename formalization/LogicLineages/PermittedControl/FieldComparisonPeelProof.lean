module
public import LogicLineages.PermittedControl.FieldComparisonTargets
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.CocycleProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-! Arithmetic over abstract naturals. -/

theorem peel_tail_cocycle (a e m r x : Nat) (h : max (max 2 (max a (max e m))) r ≤ x) :
    max 2 (max a (max e m)) ≤ x := by omega

theorem peel_tail_zero (a m r x : Nat) (h : max (max 2 (max a (max m m))) r ≤ x) :
    max 2 (max a m) ≤ x := by omega

theorem peel_tail_residue (a e m B x t : Nat)
    (h : max (max 2 (max a (max e m))) (max (m + 3) (max 1 B)) ≤ x) (hxt : x ≤ t) :
    max e (max (m + 3) (max 1 B)) ≤ t := by omega

/-! Comparison codes and table rows under a strictly increasing map. -/

theorem comparison_lt {a b : Nat} (h : a < b) : numericalComparison a b = 0 := by
  unfold numericalComparison
  rw [if_pos h]

theorem comparison_eq (a : Nat) : numericalComparison a a = 1 := by
  unfold numericalComparison
  rw [if_neg (Nat.lt_irrefl a),if_pos rfl]

theorem comparison_gt {a b : Nat} (h : b < a) : numericalComparison a b = 2 := by
  unfold numericalComparison
  rw [if_neg (Nat.lt_asymm h),if_neg (Nat.ne_of_gt h)]

theorem comparison_strictMono (g : Nat → Nat) (hg : StrictMono g) (a b : Nat) :
    numericalComparison (g a) (g b) = numericalComparison a b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [comparison_lt h,comparison_lt (hg h)]
  · rw [h,comparison_eq,comparison_eq]
  · rw [comparison_gt h,comparison_gt (hg h)]

theorem rows_strictMono (g : Nat → Nat) (hg : StrictMono g) (sign y h q p : Nat)
    (hr : InverseTableRows sign y h q p) : InverseTableRows sign y h (g q) (g p) := by
  unfold InverseTableRows at hr ⊢
  refine ⟨fun hs => ?_,fun hs => ?_,fun hs => ?_⟩
  · obtain ⟨h1,h2,h3⟩ := hr.1 hs
    exact ⟨hg.lt_iff_lt.trans h1,hg.injective.eq_iff.trans h2,hg.lt_iff_lt.trans h3⟩
  · obtain ⟨h1,h2,h3⟩ := hr.2.1 hs
    exact ⟨hg.lt_iff_lt.trans h1,fun he => h2 (hg.injective he),hg.lt_iff_lt.trans h3⟩
  · obtain ⟨h1,h2,h3⟩ := hr.2.2 hs
    exact ⟨hg.lt_iff_lt.trans h1,fun he => h2 (hg.injective he),hg.lt_iff_lt.trans h3⟩

/-- The exact row: `g y` against `g h` is decided by `y` against `h`. -/
theorem rows_exact (g : Nat → Nat) (hg : StrictMono g) (y h : Nat) :
    InverseTableRows 1 y h (g y) (g h) := by
  unfold InverseTableRows
  exact ⟨fun _ => ⟨hg.lt_iff_lt,hg.injective.eq_iff,hg.lt_iff_lt⟩,
    fun hs => absurd hs (by decide),fun hs => absurd hs (by decide)⟩

/-! Notations of `ω · c`. -/

theorem omegaNote_repr : omegaNote.1.repr = Ordinal.omega0 := by
  show ONote.repr (ONote.oadd 1 1 0) = Ordinal.omega0
  simp [ONote.repr]

theorem omegaMultiple_repr (c : Nat) :
    (omegaMultiple c).1.repr = Ordinal.omega0 * (c : Ordinal) := by
  have h := ONote.repr_mul omegaNote.1 (NONote.ofNat c).1
  have hc : ONote.repr (NONote.ofNat c).1 = (c : Ordinal) := ONote.repr_ofNat c
  rw [omegaNote_repr,hc] at h
  exact h

theorem peeled_repr (mu : NONote) (c : Nat) :
    (mu + omegaMultiple c).1.repr = mu.1.repr + Ordinal.omega0 * (c : Ordinal) := by
  rw [note_add_repr,omegaMultiple_repr]

/-! Peeling `c` applications of `f` off an entry by advancing its endpoint. -/

theorem omega_multiple_limit (c : Nat) (hc : 0 < c) :
    Order.IsSuccLimit (Ordinal.omega0 * (c : Ordinal.{0})) :=
  Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast hc)

theorem peeled_endpoint (mu : Ordinal.{0}) (hmu : mu = 0 ∨ Order.IsSuccLimit mu) (c : Nat) :
    mu + Ordinal.omega0 * (c : Ordinal) = 0 ∨
      Order.IsSuccLimit (mu + Ordinal.omega0 * (c : Ordinal)) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simpa only [Nat.cast_zero,mul_zero,add_zero] using hmu
  · exact Or.inr (Ordinal.isSuccLimit_add _ (omega_multiple_limit c hc))

/-- A long interval stays proper under every finite endpoint advance. -/
theorem long_peel_bound (lam mu : Ordinal.{0}) (hmuE : mu < epsilonZero)
    (hmu : mu = 0 ∨ Order.IsSuccLimit mu) (hll : Order.IsSuccLimit lam) (hml : mu < lam)
    (hlong : ¬ ∃ k : Nat, 0 < k ∧ lam = mu + Ordinal.omega0 * (k : Ordinal)) (c : Nat) :
    mu + Ordinal.omega0 * (c : Ordinal) < lam := by
  obtain ⟨P,j,hP,hdiv,hmuEq,hmuNorm⟩ := target_prefix_decomposition mu hmu hmuE
  have hbar := long_interval_above lam mu P j hmuEq hdiv hll hml hlong
  refine lt_of_lt_of_le ?_ hbar
  rw [hmuEq,add_assoc,← mul_add,← Nat.cast_add]
  apply (add_lt_add_iff_left P).mpr
  have h := linear_below_square (j+c) 0
  rw [Nat.cast_zero,add_zero] at h
  exact h

theorem entry_peel (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lam mu : Ordinal.{0}) (c x : Nat) (hlam : lam < epsilonZero) (hll : Order.IsSuccLimit lam)
    (hmu : mu = 0 ∨ Order.IsSuccLimit mu) (hlt : mu + Ordinal.omega0 * (c : Ordinal) < lam)
    (hx : max (max 2 (max (actualOrdinalNorm lam)
      (max (actualOrdinalNorm (mu + Ordinal.omega0 * (c : Ordinal))) (actualOrdinalNorm mu))))
      (max (actualOrdinalNorm mu + 3) (max 1 B)) ≤ x) :
    ∃ i k : Nat, FirstEntry f (countInitial lam x) (mu + Ordinal.omega0 * (c : Ordinal)) i ∧
      FirstEntry f (countInitial lam x) mu k ∧
      entryNormAt f (countInitial lam x) k = f^[c] (entryNormAt f (countInitial lam x) i) ∧
      x ≤ entryNormAt f (countInitial lam x) i := by
  have had := selected_threshold_admissible f B hf
  have hml : mu < lam := lt_of_le_of_lt le_self_add hlt
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp only [Nat.cast_zero,mul_zero,add_zero] at hx ⊢
    obtain ⟨i,hi,hn⟩ := entryExistenceOrbit f B hf lam mu x hlam hll hmu hml
      (peel_tail_zero _ _ _ _ hx)
    refine ⟨i,i,hi,hi,rfl,?_⟩
    rw [hn]
    exact iterate_self_le (control_self_le f had.2) i x
  · have hkl : Order.IsSuccLimit (mu + Ordinal.omega0 * (c : Ordinal)) :=
      Ordinal.isSuccLimit_add _ (omega_multiple_limit c hc)
    have hmk : mu < mu + Ordinal.omega0 * (c : Ordinal) := by
      simpa only [add_zero] using (add_lt_add_iff_left mu).mpr (omega_multiple_limit c hc).pos
    have hkE : mu + Ordinal.omega0 * (c : Ordinal) < epsilonZero := hlt.trans hlam
    have hmuE : mu < epsilonZero := hml.trans hlam
    obtain ⟨i,j,k,hi,hj,hk,hreset,hkij,hcont,hhi,hjN,hkN⟩ :=
      actualAffordableCocycle f B hf mu (mu + Ordinal.omega0 * (c : Ordinal)) lam x hmuE hkE hlam
        hmu hkl hll hmk hlt (peel_tail_cocycle _ _ _ _ _ hx)
    have hxh : x ≤ entryNormAt f (countInitial lam x) i := by
      rw [hhi]
      exact iterate_self_le (control_self_le f had.2) i x
    obtain ⟨i',hi',-,hshort,-⟩ := entryResidues f B hf 1 (mu + Ordinal.omega0 * (c : Ordinal)) mu
      (entryNormAt f (countInitial lam x) i) (by decide) hkE hkl hmu hmk
      (peel_tail_residue _ _ _ _ _ _ hx hxh)
    have hic : i' = c := hshort c hc rfl
    have hji : j = i' := firstEntry_unique f _ _ j i' hj hi'
    refine ⟨i,k,hi,hk,?_,hxh⟩
    rw [hcont,hjN,hji,hic]

end LogicLineages.PermittedControl.FieldComparison
