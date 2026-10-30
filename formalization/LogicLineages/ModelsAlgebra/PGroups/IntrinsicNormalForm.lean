module
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicNormalFormTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteMultiplicity
public import LogicLineages.ModelsAlgebra.PGroups.DescriptorAlgebra
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRankAssembly
public import LogicLineages.ModelsAlgebra.PGroups.FullShift
public import Mathlib.SetTheory.Cardinal.ToNat
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

private theorem length_count (t : ℕ) (ell : Fin t → ℕ) (j : ℕ) :
    (Finset.univ.filter (fun a => j+1 = ell a)).card = Nat.card {a : Fin t // ell a = j+1} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

private theorem length_count_zero (t : ℕ) (ell : Fin t → ℕ) (j : ℕ)
    (h : ∀ a, j+1 ≠ ell a) : (Finset.univ.filter (fun a => j+1 = ell a)).card = 0 := by
  classical
  have he : Finset.univ.filter (fun a => j+1 = ell a) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _
    exact h a
  rw [he, Finset.card_empty]

theorem intrinsic_full_shift_normal_form : Targets.groupIntrinsicFullShiftNormalForm := by
  classical
  intro p _ G _ _ k N hk hkN hb hf hi hlo
  let rankG : ℕ → Cardinal := fun j => Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G))
  let ml : Fin (k-1) → ℕ := fun j => (rankG j.val).toNat
  let mu : Fin (N-k) → ℕ := fun j => (rankG (k+j.val)).toNat
  letI : Finite (multipleImage G (p ^ k)) := hf
  have hu : ∀ j : Fin (N-k), rankG (k+j.val) < Cardinal.aleph0 := by
    intro j
    let S : AddSubgroup (multipleImage G (p ^ k)) := finiteFiltration p j.val
    letI : Finite (pSocle p S) := inferInstance
    letI : Finite (UlmLayer p S) := Finite.of_surjective
      (QuotientAddGroup.mk' (successorSocleSubgroup p S))
      (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p S))
    have hr := (rank_le_card (ZMod p) (UlmLayer p S)).trans_lt (Cardinal.lt_aleph0_of_finite (UlmLayer p S))
    exact lt_of_eq_of_lt (image_ulm_rank G p k j.val).symm hr
  obtain ⟨t,ell,hL,hLc⟩ := finite_multiplicity_enumeration (k-1) ml
  obtain ⟨s,u,hU,hUc⟩ := finite_multiplicity_enumeration (N-k) mu
  let r : Fin s → ℕ := fun a => k + u a
  have hell : ∀ a, 0 < ell a ∧ ell a < k := by
    intro a
    have h := hL a
    omega
  have hr : ∀ a, k < r a ∧ r a ≤ N := by
    intro a
    have h := hU a
    dsimp [r]
    omega
  refine ⟨t,ell,s,r,hell,hr,?_⟩
  apply bounded_ulm_categoricity p G (FullShiftGroup p k t ell s r) N hb
  · intro x
    apply Prod.ext
    · apply Prod.ext
      · funext a
        exact power_cyclic_annihilation p (ell a) N ((hell a).2.le.trans hkN) (x.1.1 a)
      · apply Finsupp.ext
        intro a
        exact power_cyclic_annihilation p k N hkN (x.1.2 a)
    · funext a
      exact power_cyclic_annihilation p (r a) N (hr a).2 (x.2 a)
  · intro j
    rw [full_shift_ulm_rank p k t ell s r j.val]
    by_cases hj : j.val < k-1
    · have hmid : j.val+1 ≠ k := by omega
      have hright : (Finset.univ.filter (fun a => j.val+1 = r a)).card = 0 :=
        length_count_zero s r j.val (fun a => by have h := (hr a).1; omega)
      have hleft : (Finset.univ.filter (fun a => j.val+1 = ell a)).card = ml ⟨j.val,hj⟩ := by
        rw [length_count]
        exact hLc ⟨j.val,hj⟩
      rw [hleft, hright, if_neg hmid]
      simp only [Nat.cast_zero, add_zero]
      exact (Cardinal.cast_toNat_of_lt_aleph0 (hlo j.val hj)).symm
    · have hleft : (Finset.univ.filter (fun a => j.val+1 = ell a)).card = 0 :=
        length_count_zero t ell j.val (fun a => by have h := (hell a).2; omega)
      rw [hleft]
      by_cases hm : j.val = k-1
      · have hmid : j.val+1 = k := by omega
        have hright : (Finset.univ.filter (fun a => j.val+1 = r a)).card = 0 :=
          length_count_zero s r j.val (fun a => by have h := (hr a).1; omega)
        rw [hright, if_pos hmid]
        simp only [Nat.cast_zero, zero_add, add_zero]
        exact (congrArg rankG hm).trans (middle_image_ulm_rank p G k hk hi hf)
      · have hkj : k ≤ j.val := by omega
        have hmid : j.val+1 ≠ k := by omega
        have hidx : j.val-k < N-k := by have h := j.isLt; omega
        have hright : (Finset.univ.filter (fun a => j.val+1 = r a)).card = mu ⟨j.val-k,hidx⟩ := by
          rw [length_count]
          have e : {a : Fin s // r a = j.val+1} ≃ {a : Fin s // u a = (j.val-k)+1} :=
            Equiv.subtypeEquivRight (fun a => by dsimp [r]; omega)
          exact (Nat.card_congr e).trans (hUc ⟨j.val-k,hidx⟩)
        rw [hright, if_neg hmid]
        simp only [Nat.cast_zero, zero_add]
        have hindex : k + (j.val-k) = j.val := by omega
        exact (congrArg rankG hindex).symm.trans
          (Cardinal.cast_toNat_of_lt_aleph0 (hu ⟨j.val-k,hidx⟩)).symm

theorem nonzero_lower_short_block : Targets.groupNonzeroLowerShortBlock := by
  classical
  intro p _ G _ k t s ell r hell hr ⟨e⟩ ⟨j,hj,hne⟩
  by_contra ht
  have ht0 : t = 0 := by omega
  have he := isomorphism_ulm_rank G (FullShiftGroup p k t ell s r) e p j
  have hzL : (Finset.univ.filter (fun a => j+1 = ell a)).card = 0 := by
    haveI : IsEmpty (Fin t) := by rw [ht0]; infer_instance
    simp
  have hzR : (Finset.univ.filter (fun a => j+1 = r a)).card = 0 :=
    length_count_zero s r j (fun a => by have h := hr a; omega)
  have hmid : j+1 ≠ k := by omega
  apply hne
  exact he.trans (by rw [full_shift_ulm_rank p k t ell s r j, hzL, hzR, if_neg hmid]; simp)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
