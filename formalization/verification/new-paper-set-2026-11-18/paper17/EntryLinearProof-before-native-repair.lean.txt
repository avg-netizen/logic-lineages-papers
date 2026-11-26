module
public import LogicLineages.PermittedControl.EntryExistenceProof
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem firstEntry_unique (f : Nat → Nat) (a nu : Ordinal.{0}) (i j : Nat)
    (hi : FirstEntry f a nu i) (hj : FirstEntry f a nu j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hj.2.2 i h ⟨hi.1,hi.2.1⟩)
  · exact h
  · exact False.elim (hi.2.2 j h ⟨hj.1,hj.2.1⟩)

theorem linear_below_square (k n : Nat) :
    Ordinal.omega0 * (k : Ordinal.{0}) + (n : Ordinal) < Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
  have h : Ordinal.omega0 * (k : Ordinal) + (n : Ordinal) <
      Ordinal.omega0 * ((k+1 : Nat) : Ordinal) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
      (add_lt_add_right (Ordinal.natCast_lt_omega0 n) (Ordinal.omega0 * (k : Ordinal)))
  have h' := (Ordinal.isNormal_mul_right Ordinal.omega0_pos).strictMono
    (Ordinal.natCast_lt_omega0 (k+1))
  have he : Ordinal.omega0 ^ (2 : Ordinal.{0}) = Ordinal.omega0 * Ordinal.omega0 := by
    rw [show (2 : Ordinal.{0}) = 1+1 by norm_num, Ordinal.opow_add, Ordinal.opow_one]
  rw [he]
  exact h.trans h'

theorem limit_divisible (nu : Ordinal.{0}) (hnu : nu = 0 ∨ Order.IsSuccLimit nu) : Ordinal.omega0 ∣ nu := by
  rcases hnu with rfl | hnu
  · exact dvd_zero _
  · exact Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hnu.isSuccPrelimit

theorem linear_entry (f : Nat → Nat) (hf : ∀ n, G n ≤ f n)
    (nu : Ordinal.{0}) (hnu : nu = 0 ∨ Order.IsSuccLimit nu) (heps : nu < epsilonZero)
    (k n : Nat) : FirstEntry f (nu + (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))) nu k := by
  let c := actualOrdinalNorm nu
  let g := prefixRemainderControl f c
  have hg : ∀ x : Nat, x ≤ g x := by
    intro x
    have h := control_self_le f hf (c+x)
    dsimp [g,prefixRemainderControl]
    omega
  have hmin : actualMinExponentAtLeast nu (1 : Ordinal) := by
    apply (actualMinExponentDivisibility nu heps 1).mpr
    simpa only [Ordinal.opow_one] using limit_divisible nu hnu
  have hr : Ordinal.omega0 * (k : Ordinal) + (n : Ordinal) < Ordinal.omega0 ^ ((1 : Ordinal)+1) := by
    convert linear_below_square k n using 1 <;> norm_num
  have hbudget : ∀ x : Nat, actualOrdinalNorm nu ≤ f (actualOrdinalNorm nu+x) := by
    intro x
    exact (Nat.le_add_right _ _).trans (control_self_le f hf _)
  have htrace := actualPrefixControlTrace f nu (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))
    heps (finiteCoefficient_below k n) 1 (by norm_num) hmin hr hbudget
  have hc : actualControlledCount g (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) = k :=
    actualExpansiveControlLinearCount g hg k n
  change (∀ i : Nat, i ≤ actualControlledCount g _ → _ ) ∧ _ at htrace
  rw [hc] at htrace
  have hstate : (descentWith f)^[k] (nu + (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal))) =
      nu + actualControlledStateAfter g (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) k := htrace.1 k le_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hstate]
    exact le_self_add
  · rw [hstate]
    exact (add_lt_add_iff_left nu).mpr htrace.2.1
  · intro j hj hhit
    have h := htrace.2.2 j hj
    exact (not_lt_of_ge h) hhit.2

end LogicLineages.PermittedControl
