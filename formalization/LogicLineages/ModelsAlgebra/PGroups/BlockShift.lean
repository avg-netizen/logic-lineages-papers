module

public import LogicLineages.ModelsAlgebra.PGroups.BlockShiftTargets
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open scoped BigOperators

theorem finite_block_coordinates : Targets.groupFiniteBlockCoordinates := by
  classical
  intro p k t ℓ h a
  constructor
  · intro j
    simp only [finiteBlockInsert, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply,
      Pi.evalAddMonoidHom_apply, Finsupp.singleAddHom_apply, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      exact Finsupp.single_eq_of_ne (fun hval => hbj (Fin.ext hval.symm))
    · simp
  · intro i
    simp only [finiteBlockInsert, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply,
      Pi.evalAddMonoidHom_apply, Finsupp.singleAddHom_apply, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    exact Finsupp.single_eq_of_ne (by have := j.isLt; omega)

theorem block_shift_coordinates : Targets.groupBlockShiftCoordinates := by
  intro p k t ℓ h x
  constructor
  · rfl
  constructor
  · intro j
    have hz : Finsupp.mapDomain (fun i : ℕ => t + i) x.2 j.val = 0 :=
      Finsupp.mapDomain_notin_range (f := fun i : ℕ => t + i) x.2 j.val (by
        rintro ⟨i, hi⟩
        change t + i = j.val at hi
        have hj : j.val < t := j.isLt
        omega)
    simpa [blockShiftHom, hz] using (finite_block_coordinates p k t ℓ h x.1).1 j
  · intro i
    have ht := Finsupp.mapDomain_apply (f := fun a : ℕ => t + a)
      (fun a b (hab : t + a = t + b) => Nat.add_left_cancel hab) x.2 i
    simpa [blockShiftHom, (finite_block_coordinates p k t ℓ h x.1).2 i] using ht

theorem block_shift_injective : Targets.groupBlockShiftInjective := by
  intro p _ k t ℓ h x y he
  apply Prod.ext
  · funext j
    apply power_cyclic_inclusion_injective p (ℓ j) k (h j)
    simpa only [(block_shift_coordinates p k t ℓ h x).2.1 j,
      (block_shift_coordinates p k t ℓ h y).2.1 j] using
      congrArg (fun z : BlockShiftGroup p k t ℓ => z.2 j.val) he
  · apply Finsupp.ext
    intro i
    simpa only [(block_shift_coordinates p k t ℓ h x).2.2 i,
      (block_shift_coordinates p k t ℓ h y).2.2 i] using
      congrArg (fun z : BlockShiftGroup p k t ℓ => z.2 (t + i)) he

theorem power_finsupp_socle_roots : Targets.groupPowerFinsuppSocleRoots := by
  classical
  intro p _ k hk v hv
  let root : ZMod (p ^ k) → ZMod (p ^ k) := fun a =>
    if h0 : a = 0 then 0 else
      if ha : p • a = 0 then Classical.choose (power_cyclic_socle_roots p k hk a ha) else 0
  have hzero : root 0 = 0 := by simp [root]
  have hroot (a : ZMod (p ^ k)) (ha : p • a = 0) : p ^ (k - 1) • root a = a := by
    by_cases h0 : a = 0
    · simp [root, h0]
    · simp only [root, dif_neg h0, dif_pos ha]
      exact Classical.choose_spec (power_cyclic_socle_roots p k hk a ha)
  refine ⟨v.mapRange root hzero, ?_⟩
  apply Finsupp.ext
  intro i
  change p ^ (k - 1) • root (v i) = v i
  apply hroot
  simpa using congrArg (fun w : ℕ →₀ ZMod (p ^ k) => w i) hv

theorem block_shift_socle_roots : Targets.groupBlockShiftSocleRoots := by
  intro p _ k t hk ℓ h x hx
  have hz : p • blockShiftHom p k t ℓ h x = 0 := by
    simpa only [map_nsmul, map_zero] using congrArg (blockShiftHom p k t ℓ h) hx
  have hv : p • (blockShiftHom p k t ℓ h x).2 = 0 := congrArg Prod.snd hz
  obtain ⟨w, hw⟩ := power_finsupp_socle_roots p k hk _ hv
  refine ⟨(0, w), ?_⟩
  apply Prod.ext
  · change p ^ (k - 1) • (0 : ∀ j : Fin t, ZMod (p ^ ℓ j)) = (blockShiftHom p k t ℓ h x).1
    simpa only [nsmul_zero] using (block_shift_coordinates p k t ℓ h x).1.symm
  · exact hw

theorem block_short_no_root : Targets.groupBlockShortNoRoot := by
  classical
  intro p _ k t ℓ j hj hk
  have hw := power_cyclic_socle_witness p (ℓ j) hj
  constructor
  · apply Prod.ext
    · funext i
      by_cases hi : i = j
      · subst i
        simpa [blockShortWitness] using hw.1
      · simp [blockShortWitness, Pi.single_eq_of_ne hi]
    · simp [blockShortWitness]
  · rintro ⟨y, hy⟩
    have he := congrArg (fun z : BlockShiftGroup p k t ℓ => z.1 j) hy
    have hz := power_cyclic_annihilation p (ℓ j) (k - 1) (by omega) (y.1 j)
    have he' : p ^ (k - 1) • y.1 j = ((p ^ (ℓ j - 1) : ℕ) : ZMod (p ^ ℓ j)) := by
      simpa [blockShortWitness] using he
    exact hw.2 (hz.symm.trans he').symm

theorem block_shift_exponent : Targets.groupBlockShiftExponent := by
  intro p k t ℓ h x
  apply Prod.ext
  · funext j
    exact power_cyclic_annihilation p (ℓ j) k (h j) (x.1 j)
  · apply Finsupp.ext
    intro i
    exact ZModModule.char_nsmul_eq_zero (p ^ k) (x.2 i)

theorem block_shift_countable : Targets.groupBlockShiftCountable := by
  intro p _ k t ℓ
  infer_instance

theorem block_shift_infinite : Targets.groupBlockShiftInfinite := by
  intro p _ k t ℓ hk
  letI : Fact (1 < p ^ k) := ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)⟩
  infer_instance

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
