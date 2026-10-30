module
public import LogicLineages.OrdinalComparison.RestrictedPartitionTargets
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Subtype
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem restrictedPartitionCoordinateBound : Targets.RestrictedPartitionCoordinateBound := by
  intro d n a i
  have hs : (i.val + 1) * a.1 i ≤ restrictedPartitionWeight a.1 :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((j.val + 1) * a.1 j)) (Finset.mem_univ i)
  have hm : a.1 i ≤ (i.val + 1) * a.1 i := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  exact (hm.trans hs).trans_eq a.2

theorem restrictedPartitionFinite : Targets.RestrictedPartitionFinite := by
  intro d n
  let encode : RestrictedPartitionState d n → (Fin d → Fin (n + 1)) :=
    fun a i => ⟨a.1 i, Nat.lt_succ_of_le (restrictedPartitionCoordinateBound d n a i)⟩
  apply Finite.of_injective encode
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrArg (fun f : Fin d → Fin (n + 1) => (f i).val) hab

private theorem partition_weight_init (d : Nat) (a : Fin (d + 1) → Nat) :
    restrictedPartitionWeight a = restrictedPartitionWeight (Fin.init a) + (d + 1) * a (Fin.last d) := by
  unfold restrictedPartitionWeight
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem partition_weight_snoc (d : Nat) (a : Fin d → Nat) (j : Nat) :
    restrictedPartitionWeight (Fin.snoc a j) = restrictedPartitionWeight a + (d + 1) * j := by
  rw [partition_weight_init]
  simp only [Fin.init_snoc, Fin.snoc_last]

theorem restrictedPartitionUnitCount : Targets.RestrictedPartitionUnitCount := by
  intro n
  let e : RestrictedPartitionState 1 n ≃ Unit := {
    toFun := fun _ => Unit.unit
    invFun := fun _ => ⟨fun _ => n, by simp [restrictedPartitionWeight]⟩
    left_inv := by
      intro a
      apply Subtype.ext
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have h := a.2
      simpa [restrictedPartitionWeight] using h.symm
    right_inv := by intro u; cases u; rfl }
  change Nat.card (RestrictedPartitionState 1 n) = 1
  rw [Nat.card_congr e]
  simp

private def partition_split (d n : Nat) (a : RestrictedPartitionState (d + 1) n) :
    (j : Fin (n / (d + 1) + 1)) × RestrictedPartitionState d (n - (d + 1) * j.val) := by
  have hw := partition_weight_init d a.1
  have hs : restrictedPartitionWeight (Fin.init a.1) + (d + 1) * a.1 (Fin.last d) = n :=
    hw.symm.trans a.2
  have hj : a.1 (Fin.last d) ≤ n / (d + 1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos d)).mpr
    have hcharge : (d + 1) * a.1 (Fin.last d) ≤ n := by omega
    simpa only [Nat.mul_comm] using hcharge
  refine ⟨⟨a.1 (Fin.last d), Nat.lt_succ_of_le hj⟩, ⟨Fin.init a.1, ?_⟩⟩
  change restrictedPartitionWeight (Fin.init a.1) = n - (d + 1) * a.1 (Fin.last d)
  omega

private def partition_join (d n : Nat)
    (s : (j : Fin (n / (d + 1) + 1)) × RestrictedPartitionState d (n - (d + 1) * j.val)) :
    RestrictedPartitionState (d + 1) n := by
  refine ⟨Fin.snoc s.2.1 s.1.val, ?_⟩
  rw [partition_weight_snoc, s.2.2]
  have hj : s.1.val ≤ n / (d + 1) := Nat.le_of_lt_succ s.1.isLt
  have hcharge : (d + 1) * s.1.val ≤ n := by
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (Nat.succ_pos d)).mp hj
  omega

private def partition_split_equiv (d n : Nat) :
    RestrictedPartitionState (d + 1) n ≃
      ((j : Fin (n / (d + 1) + 1)) × RestrictedPartitionState d (n - (d + 1) * j.val)) where
  toFun := partition_split d n
  invFun := partition_join d n
  left_inv := by
    intro a
    apply Subtype.ext
    change Fin.snoc (Fin.init a.1) (a.1 (Fin.last d)) = a.1
    exact Fin.snoc_init_self a.1
  right_inv := by
    rintro ⟨j, a⟩
    apply Sigma.ext
    · apply Fin.ext
      change Fin.snoc (α := fun _ : Fin (d + 1) => Nat) a.1 j.val (Fin.last d) = j.val
      exact Fin.snoc_last _ _
    · simp only [partition_split, partition_join, Fin.snoc_last, Fin.init_snoc]
      apply (Subtype.heq_iff_coe_eq (by intro x; simp only [Fin.snoc_last])).mpr
      rfl

theorem restrictedPartitionLastCoordinateRecurrence : Targets.RestrictedPartitionLastCoordinateRecurrence := by
  classical
  intro d n
  letI (j : Fin (n / (d + 1) + 1)) : Finite (RestrictedPartitionState d (n - (d + 1) * j.val)) :=
    restrictedPartitionFinite d _
  change Nat.card (RestrictedPartitionState (d + 1) n) = _
  rw [Nat.card_congr (partition_split_equiv d n), Nat.card_sigma]
  change (∑ j : Fin (n / (d + 1) + 1), restrictedPartitionCount d (n - (d + 1) * j.val)) = _
  exact Fin.sum_univ_eq_sum_range (fun j : Nat => restrictedPartitionCount d (n - (d + 1) * j)) _

end LogicLineages.OrdinalComparison
