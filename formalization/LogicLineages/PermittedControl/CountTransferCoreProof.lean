module
public import LogicLineages.PermittedControl.CountTransferTargets
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.CocycleProof

public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-! Arithmetic over abstract naturals: no decision procedure sees an
ordinal-norm term. -/

theorem core_count_arith (b NP j Nmu i k cnt : Nat) (heven : b % 2 = 0) (hN : Nmu = NP + 2*j)
    (hb : Nmu + 3 ≤ b) (hcnt : cnt = (b - NP)/2 - j + 1) (hk : k = i + cnt) :
    2 * (k : Int) = (b : Int) + 2 * (i : Int) + 2 * (1 - (((Nmu + 1)/2 : Nat) : Int)) := by
  omega

theorem core_tail_left (a m x : Nat) (h : max a (m + 3) ≤ x) : a ≤ x ∧ m + 3 ≤ x := by omega

theorem core_cocycle_tail (a e m x : Nat) (h : max a (m + 3) ≤ x) (he : e ≤ m + 3) :
    max 2 (max a (max e m)) ≤ x := by omega

theorem core_eta_norm (e NP j Nmu : Nat) (he : e = NP + 3) (hN : Nmu = NP + 2*j) :
    e ≤ Nmu + 3 := by omega

/-- `μ + ω²` absorbs the `ω`-tail of `μ`. -/
theorem eta_prefix (mu P : Ordinal.{0}) (j : Nat) (hmu : mu = P+Ordinal.omega0*(j : Ordinal)) :
    mu+Ordinal.omega0 ^ (2 : Ordinal.{0}) = P+Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
  rw [hmu,add_assoc]
  congr 1
  have h := linear_below_square j 0
  rw [Nat.cast_zero,add_zero] at h
  exact Ordinal.add_of_omega0_opow_le h le_rfl

/-- One exact passage through the funnel `P + ω²`: the actual first entry
into the target and its exact event count. This is the funnel branch of
the long-entry residue proof, with the count kept instead of its residue. -/
theorem funnel_exit (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (nu P : Ordinal.{0}) (j : Nat)
    (hnu : nu = 0 ∨ Order.IsSuccLimit nu) (hP : P < epsilonZero)
    (hdiv : Ordinal.omega0 ^ (2 : Ordinal.{0}) ∣ P)
    (hnuEq : nu = P+Ordinal.omega0*(j : Ordinal))
    (hnuNorm : actualOrdinalNorm nu = actualOrdinalNorm P+2*j)
    (a : Ordinal.{0}) (_ha : a < epsilonZero)
    (heq : actualLimitPart a = P+Ordinal.omega0 ^ (2 : Ordinal.{0}))
    (ht : actualOrdinalNorm nu+3 ≤ actualOrdinalNorm a) :
    FirstEntry f a nu ((f (actualOrdinalNorm a)-actualOrdinalNorm P)/2-j+1) := by
  have had := selected_threshold_admissible f B hf
  have hpow : Ordinal.omega0 ^ (2 : Ordinal.{0}) < Ordinal.omega0 ^ ((2 : Ordinal)+1) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_add_one_iff.mpr le_rfl)
  have hsigma := actualDivisiblePrefixNormAddition P (Ordinal.omega0 ^ (2 : Ordinal))
    hP square_facts.1 2 hdiv hpow
  have hsigNorm : actualOrdinalNorm (P+Ordinal.omega0 ^ (2 : Ordinal.{0})) = actualOrdinalNorm P+3 := by
    rw [hsigma.2,square_facts.2.1]
  have hnuBelow : nu+Ordinal.omega0 < P+Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
    rw [hnuEq,add_assoc]
    apply (add_lt_add_iff_left P).mpr
    have h := linear_below_square (j+1) 0
    simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,Nat.cast_zero,add_zero] using h
  have hnuEps : nu < epsilonZero := (lt_of_le_of_lt le_self_add hnuBelow).trans hsigma.1
  have hno : ¬ (nu ≤ a ∧ a < nu+Ordinal.omega0) := by
    intro h
    exact (not_lt_of_ge (hnuBelow.le.trans (heq.ge.trans (Ordinal.mul_div_le a Ordinal.omega0)))) h.2
  have hb : actualOrdinalNorm nu+3 ≤ f (actualOrdinalNorm a) :=
    ht.trans (control_self_le f had.2 _)
  let b := f (actualOrdinalNorm a)
  let q := (b-actualOrdinalNorm P)/2
  let r := (b-actualOrdinalNorm P)%2
  have hmin : actualMinExponentAtLeast P (2 : Ordinal) := (actualMinExponentDivisibility P hP 2).mpr hdiv
  have hmax := actualDivisiblePrefixMaximum P (Ordinal.omega0 ^ (2 : Ordinal)) hP square_facts.1
    square_facts.2.2.bot_lt 2 hmin hpow b (by dsimp [b]; omega)
  have hbudget : 2 ≤ b-actualOrdinalNorm P := by dsimp [b]; omega
  have hstep : descentWith f a = P+(Ordinal.omega0*(q : Ordinal)+(r : Ordinal)) := by
    unfold descentWith
    rw [heq,hmax,actualOmegaSquaredMaximum _ hbudget]
  have hq : j ≤ q := by dsimp [q,b]; omega
  have hstate : descentWith f a = nu+(Ordinal.omega0*((q-j : Nat) : Ordinal)+(r : Ordinal)) := by
    rw [hstep,hnuEq,add_assoc,← add_assoc (Ordinal.omega0 * (j : Ordinal)),← mul_add]
    simp only [← Nat.cast_add, Nat.add_sub_of_le hq]
  have hentry := linear_entry f had.2 nu hnu hnuEps (q-j) r
  rw [← hstate] at hentry
  exact firstEntry_step f a nu (q-j) hno hentry

theorem countCore : Targets.CountCore := by
  intro f B hf lam mu x hlam hll hmu hml hlong hx
  have had := selected_threshold_admissible f B hf
  have hmuEps : mu < epsilonZero := hml.trans hlam
  obtain ⟨P,j,hP,hdiv,hmuEq,hmuNorm⟩ := target_prefix_decomposition mu hmu hmuEps
  have heta := eta_prefix mu P j hmuEq
  have hbar := long_interval_above lam mu P j hmuEq hdiv hll hml hlong
  rw [heta]
  refine ⟨hbar,?_⟩
  have hpow : Ordinal.omega0 ^ (2 : Ordinal.{0}) < Ordinal.omega0 ^ ((2 : Ordinal)+1) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_add_one_iff.mpr le_rfl)
  have hsigma := actualDivisiblePrefixNormAddition P (Ordinal.omega0 ^ (2 : Ordinal))
    hP square_facts.1 2 hdiv hpow
  have hetaNorm : actualOrdinalNorm (P+Ordinal.omega0 ^ (2 : Ordinal.{0})) = actualOrdinalNorm P+3 := by
    rw [hsigma.2,square_facts.2.1]
  have hetaLim : Order.IsSuccLimit (P+Ordinal.omega0 ^ (2 : Ordinal.{0})) :=
    Ordinal.isSuccLimit_add P square_facts.2.2
  have hxs := core_tail_left _ _ _ hx
  have heven : ∀ n : Nat, f n % 2 = 0 := fun n => Nat.mod_eq_zero_of_dvd (selected_even f B hf n)
  rcases hbar.eq_or_lt with heq | hlt
  · -- identity prefix: the canonical start already has limit part `η`
    have hA := count_initial_facts lam x hlam hll hxs.1
    have hid := identityEntry f lam x hlam (Or.inr hll) hxs.1
    have hlp : actualLimitPart (countInitial lam x) = P+Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
      rw [heq]
      exact limitPart_tail lam hll _
    have hexit := funnel_exit f B hf mu P j hmu hP hdiv hmuEq hmuNorm (countInitial lam x) hA.1 hlp
      (by rw [hA.2.1]; exact hxs.2)
    rw [hA.2.1] at hexit
    refine ⟨0,_,?_,hexit,hid.2,?_⟩
    · rw [heq]
      exact hid.1
    · rw [hid.2]
      exact core_count_arith (f x) _ j _ 0 _ _ (heven x) hmuNorm
        (hxs.2.trans (control_self_le f had.2 x)) rfl (Nat.zero_add _).symm
  · -- proper prefix: cocycle through `η`, then one funnel passage
    have hmueta : mu < P+Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
      rw [← heta]
      simpa only [add_zero] using (add_lt_add_iff_left mu).mpr square_facts.2.2.pos
    obtain ⟨i,j',k,hi,hj,hk,hreset,hkij,hcont,hhi,hjN,hkN⟩ :=
      actualAffordableCocycle f B hf mu (P+Ordinal.omega0 ^ (2 : Ordinal.{0})) lam x hmuEps hsigma.1
        hlam hmu hetaLim hll hmueta hlt
        (core_cocycle_tail _ _ _ _ hx (core_eta_norm _ _ j _ hetaNorm hmuNorm))
    have hxh : x ≤ entryNormAt f (countInitial lam x) i := by
      rw [hhi]
      exact iterate_self_le (control_self_le f had.2) i x
    have hA := count_initial_facts (P+Ordinal.omega0 ^ (2 : Ordinal.{0}))
      (entryNormAt f (countInitial lam x) i) hsigma.1 hetaLim
      ((core_eta_norm _ _ j _ hetaNorm hmuNorm).trans (hxs.2.trans hxh))
    have hexit := funnel_exit f B hf mu P j hmu hP hdiv hmuEq hmuNorm _ hA.1
      (limitPart_tail _ hetaLim _) (by rw [hA.2.1]; exact hxs.2.trans hxh)
    rw [hA.2.1] at hexit
    have hjeq := firstEntry_unique f _ mu j' _ hj hexit
    refine ⟨i,k,hi,hk,hhi,?_⟩
    exact core_count_arith (f (entryNormAt f (countInitial lam x) i)) _ j _ i k _ (heven _) hmuNorm
      ((hxs.2.trans hxh).trans (control_self_le f had.2 _)) rfl (by rw [hkij,hjeq])

end LogicLineages.PermittedControl
