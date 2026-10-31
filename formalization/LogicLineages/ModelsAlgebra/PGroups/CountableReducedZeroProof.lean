module
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.Nat.Factorization.Induction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem p_primary_divisible_from_p_surjective : Targets.pPrimaryDivisibleFromPSurjective := by
  intro G _ p _ hG hpSurj
  have hprime (q : ℕ) (hq : q.Prime) : ∀ x : G, ∃ y : G, q • y = x := by
    by_cases he : q = p
    · subst q
      exact hpSurj
    · intro x
      obtain ⟨k,hk⟩ := hG x
      have hd : addOrderOf x ∣ p^k := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hk
      have hcp : p.Coprime q := (Nat.coprime_primes (Fact.out : p.Prime) hq).mpr (Ne.symm he)
      have hc : (Nat.card (AddSubgroup.zmultiples x)).Coprime q := by
        rw [Nat.card_zmultiples]
        exact Nat.Coprime.of_dvd_left hd (hcp.pow_left k)
      obtain ⟨y,hy⟩ := (Nat.Coprime.nsmul_right_bijective (G := AddSubgroup.zmultiples x) hc).2
        ⟨x,AddSubgroup.mem_zmultiples x⟩
      exact ⟨y,congrArg Subtype.val hy⟩
  refine Nat.recOnMul (motive := fun n => n ≠ 0 → ∀ x : G, ∃ y : G, n • y = x) ?_ ?_ ?_ ?_
  · intro h
    exact (h rfl).elim
  · intro _ x
    exact ⟨x,one_nsmul x⟩
  · intro q hq _
    exact hprime q hq
  · intro a b ha hb hab x
    obtain ⟨y,hy⟩ := hb (right_ne_zero_of_mul hab) x
    obtain ⟨z,hz⟩ := ha (left_ne_zero_of_mul hab) y
    exact ⟨z,by rw [mul_nsmul,hz,hy]⟩

theorem countable_p_filtration_stabilizes : Targets.countablePFiltrationStabilizes := by
  classical
  intro G _ _ p
  by_contra hn
  let κ : Ordinal.{0} := (Order.succ (Cardinal.aleph0 : Cardinal.{0})).ord
  let β (i : κ.ToType) := Ordinal.typein (α := κ.ToType) (· < ·) i
  have hcount (i : κ.ToType) : Countable (β i).ToType := by
    apply Cardinal.mk_le_aleph0_iff.mp
    rw [Cardinal.mk_toType]
    have hi : β i < κ := Ordinal.typein_lt_self i
    exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hi)
  have hdrop (i : κ.ToType) : ∃ x : G,
      x ∈ transfiniteFiltration p (β i) ∧ x ∉ transfiniteFiltration p (β i+1) := by
    have hnot : ¬(transfiniteFiltration p (β i) : AddSubgroup G) ≤ transfiniteFiltration p (β i+1) := by
      intro hle
      apply hn
      exact ⟨β i,hcount i,le_antisymm (transfiniteFiltration_antitone p le_self_add) hle⟩
    exact Set.not_subset.mp hnot
  choose x hx hxn using hdrop
  have hinj : Function.Injective x := by
    intro i j he
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply hxn i
      rw [he]
      have hb : β i < β j := (Ordinal.typein_lt_typein (α := κ.ToType) (· < ·)).mpr hij
      exact transfiniteFiltration_antitone p (Order.add_one_le_iff.mpr hb) (hx j)
    · apply hxn j
      rw [← he]
      have hb : β j < β i := (Ordinal.typein_lt_typein (α := κ.ToType) (· < ·)).mpr hji
      exact transfiniteFiltration_antitone p (Order.add_one_le_iff.mpr hb) (hx i)
  letI : Countable κ.ToType := hinj.countable
  have hc : Order.succ (Cardinal.aleph0 : Cardinal.{0}) ≤ Cardinal.aleph0 := by
    simpa only [Cardinal.mk_toType,κ,Cardinal.card_ord] using (Cardinal.mk_le_aleph0 (α := κ.ToType))
  exact (not_le_of_gt (Order.lt_succ Cardinal.aleph0)) hc

theorem countable_reduced_zero_limit : Targets.countableReducedZeroLimit := by
  intro G _ _ p _ hG hred
  obtain ⟨α,hcount,hstable⟩ := countable_p_filtration_stabilizes G p
  letI : Countable α.ToType := hcount
  let S := (transfiniteFiltration p α : AddSubgroup G)
  have hsPrimary : ∀ x : S, ∃ k : ℕ, p^k • x = 0 := by
    intro x
    obtain ⟨k,hk⟩ := hG x
    exact ⟨k,Subtype.ext hk⟩
  have hsSurj : ∀ x : S, ∃ y : S, p • y = x := by
    intro x
    have hx : (x : G) ∈ transfiniteFiltration p (α+1) := by
      rw [hstable]
      exact x.property
    rw [transfiniteFiltration_add_one] at hx
    obtain ⟨y,hy,he⟩ := hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  have hz : S = ⊥ := hred S (p_primary_divisible_from_p_surjective S p hsPrimary hsSurj)
  refine ⟨α+Ordinal.omega0, ?_, Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0, ?_⟩
  · apply Cardinal.mk_le_aleph0_iff.mp
    rw [Cardinal.mk_toType,Ordinal.card_add,Ordinal.card_omega0]
    have h : α.card ≤ Cardinal.aleph0 := by
      simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := α.ToType))
    exact (add_le_add h le_rfl).trans_eq Cardinal.aleph0_add_aleph0
  · exact le_antisymm ((transfiniteFiltration_antitone p le_self_add).trans hz.le) bot_le
end LogicLineages.ModelsAlgebra.PGroups
