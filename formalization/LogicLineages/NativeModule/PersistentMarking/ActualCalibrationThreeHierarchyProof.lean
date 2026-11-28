module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePsiTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeLevelProof

@[expose] public section

/-! Function side of n = 3 (no ψ): `N_B` doubles (`y + y ≤ N_B y`), positive fixed points of a
level enumeration `E_β` are limits closed under addition, under `D β` and under `D β`-orbits,
strict T3, `D e Γ_0 = D e 0` for `e ≥ 1`, and the facts about `L = (β ↦ D β 0)`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

/-! Small generic helpers. -/

theorem ozl (x : Ordinal.{0}) : (0 : Ordinal.{0}) ≤ x := not_lt.mp not_lt_zero

theorem one_add_one_lt_omega : (1 : Ordinal.{0}) + 1 < ω := by
  have two_lt : (2 : Ordinal.{0}) < ω := by exact_mod_cast nat_lt_omega0 2
  rw [one_add_one_eq_two]
  exact two_lt

/-- An opaque countable ordinal with a prescribed value. -/
theorem countable_mk (x : Ordinal.{0}) (h : x < ω₁) : ∃ c : CountableOrdinal, c.val = x :=
  ⟨mkCountable x h, rfl⟩

theorem countable_cases (θ : CountableOrdinal) :
    θ.val = 0 ∨ (∃ c : CountableOrdinal, θ.val = c.val + 1) ∨ Order.IsSuccLimit θ.val := by
  rcases zero_or_succ_or_isSuccLimit θ.val with h0 | ⟨c, hc⟩ | hl
  · exact Or.inl h0
  · have hcl : c < θ.val := by rw [← hc]; exact Order.lt_succ c
    exact Or.inr (Or.inl ⟨mkCountable c (hcl.trans (countable_val_lt θ)),
      hc.symm.trans (Ordinal.add_one_eq_succ c).symm⟩)
  · exact Or.inr (Or.inr hl)

theorem orbit_limit_le (f : CountableOrdinal → CountableOrdinal) (x l : CountableOrdinal)
    (hl : Order.IsSuccLimit l.val) (c : Ordinal.{0})
    (H : ∀ β : CountableOrdinal, β.val < l.val → (orbit .base f x β).val ≤ c) :
    (orbit .base f x l).val ≤ c := by
  rw [orbit_limit_eq f x l hl]
  exact ciSup_le' (fun e => H (earlierStage l e) e.property)

theorem lt_orbit_limit (f : CountableOrdinal → CountableOrdinal) (x l : CountableOrdinal)
    (hl : Order.IsSuccLimit l.val) (y : Ordinal.{0}) (h : y < (orbit .base f x l).val) :
    ∃ β : CountableOrdinal, β.val < l.val ∧ y < (orbit .base f x β).val := by
  haveI : Nonempty (EarlierStages l) := ⟨⟨0, hl.bot_lt⟩⟩
  rw [orbit_limit_eq f x l hl] at h
  obtain ⟨e, he⟩ := (lt_ciSup_iff
    (bddAbove_orbit .base f (fun e : EarlierStages l => orbit .base f x (earlierStage l e)))).1 h
  exact ⟨earlierStage l e, e.property, he⟩

theorem add_self_le_opow (c : Ordinal.{0}) : c + c ≤ (ω : Ordinal.{0}) ^ (c + 1) := by
  have e : c + c = c * Order.succ 1 := by rw [Ordinal.mul_succ, mul_one]
  rw [e, Ordinal.opow_add_one]
  exact mul_le_mul' (Ordinal.right_le_opow c one_lt_omega0) (Order.succ_le_of_lt one_lt_omega0)

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

/-! Levels: the orbit equations in `level` form. -/

theorem level_zero_eq (z : CountableOrdinal) (hz : z.val = 0) :
    level fix pow z = veblenValue fix pow :=
  (orbitEquations (tier 1) (towerValue fix 0) (veblenValue fix pow)).1 z hz

theorem level_limit (l : CountableOrdinal) (hl : Order.IsSuccLimit l.val) (x : CountableOrdinal) :
    (level fix pow l x).val = ⨆ e : EarlierStages l, (level fix pow (earlierStage l e) x).val :=
  (orbitEquations (tier 1) (towerValue fix 0) (veblenValue fix pow)).2.2 l hl x

theorem level_limit_le (l : CountableOrdinal) (hl : Order.IsSuccLimit l.val) (x : CountableOrdinal)
    (c : Ordinal.{0}) (H : ∀ β : CountableOrdinal, β.val < l.val → (level fix pow β x).val ≤ c) :
    (level fix pow l x).val ≤ c := by
  rw [level_limit l hl x]
  exact ciSup_le' (fun e => H (earlierStage l e) e.property)

theorem lt_level_limit (l : CountableOrdinal) (hl : Order.IsSuccLimit l.val) (x : CountableOrdinal)
    (y : Ordinal.{0}) (h : y < (level fix pow l x).val) :
    ∃ β : CountableOrdinal, β.val < l.val ∧ y < (level fix pow β x).val := by
  haveI : Nonempty (EarlierStages l) := ⟨⟨0, hl.bot_lt⟩⟩
  rw [level_limit l hl x] at h
  obtain ⟨e, he⟩ := (lt_ciSup_iff
    (bddAbove_orbit .base id (fun e : EarlierStages l => level fix pow (earlierStage l e) x))).1 h
  exact ⟨earlierStage l e, e.property, he⟩

theorem level_monoInfl (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β : CountableOrdinal) :
    MonoInfl (level fix pow β) :=
  (levelInvariant Z s add mul w one pow fix h1 h2).1 β

theorem level_mono_index (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (α β : CountableOrdinal)
    (h : α.val ≤ β.val) (x : CountableOrdinal) :
    (level fix pow α x).val ≤ (level fix pow β x).val :=
  (levelInvariant Z s add mul w one pow fix h1 h2).2.1 α β h x

/-- T3 in `levelEnum` form: `D (β+1) x` is the least fixed point of `E_β` above `x`. -/
theorem level_step (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β β' : CountableOrdinal)
    (hβ : β'.val = β.val + 1) (x : CountableOrdinal) :
    levelEnum fix pow β (level fix pow β' x) = level fix pow β' x ∧
    x.val < (level fix pow β' x).val ∧
    ∀ θ : CountableOrdinal, x.val < θ.val → levelEnum fix pow β θ = θ →
      (level fix pow β' x).val ≤ θ.val :=
  (levelInvariant Z s add mul w one pow fix h1 h2).2.2 β β' hβ x

/-! The enumerations `E_β`. -/

theorem lvEnum_succ (β a a' : CountableOrdinal) (h : a'.val = a.val + 1) :
    levelEnum fix pow β a' = level fix pow β (levelEnum fix pow β a) :=
  orbit_succ (level fix pow β) zeroValue a a' h

theorem lvEnum_zero (β a : CountableOrdinal) (h : a.val = 0) : levelEnum fix pow β a = zeroValue :=
  orbit_zero (level fix pow β) zeroValue a h

theorem lvEnum_strict (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β a b : CountableOrdinal)
    (h : a.val < b.val) : (levelEnum fix pow β a).val < (levelEnum fix pow β b).val :=
  orbit_strictMono (level fix pow β) zeroValue (level_monoInfl h1 h2 β).2 a b h

theorem lvEnum_mono (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β a b : CountableOrdinal)
    (h : a.val ≤ b.val) : (levelEnum fix pow β a).val ≤ (levelEnum fix pow β b).val :=
  orbit_mono (level fix pow β) zeroValue (level_monoInfl h1 h2 β).2 h

theorem lvEnum_id_le (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β a : CountableOrdinal) :
    a.val ≤ (levelEnum fix pow β a).val :=
  orbit_id_le (level fix pow β) zeroValue (level_monoInfl h1 h2 β).2 a

/-! Doubling. -/

/-- The value of `fix f z` dominates stage two: `f (f (s z)) ≤ fix f z`. -/
theorem fix_ge_stage_two (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (f : CountableOrdinal → CountableOrdinal) (z : CountableOrdinal) :
    (f (f (s z))).val ≤ (fix f z).val := by
  have wlim : Order.IsSuccLimit w.val := by rw [h2.1]; exact isSuccLimit_omega0
  let z0 := mkCountable 0 zero_lt_omegaOne
  let o1 := mkCountable 1 one_lt_index
  have two_lt : (2 : Ordinal.{0}) < ω := by exact_mod_cast nat_lt_omega0 2
  let o2 := mkCountable 2 (two_lt.trans omega0_lt_omega_one)
  have h2lt : o2.val < w.val := by
    rw [h2.1]
    exact two_lt
  have le := orbit_le_limit f (s z) w wlim o2 h2lt
  rw [orbit_succ f (s z) o1 o2 (by show (2 : Ordinal.{0}) = 1 + 1; exact one_add_one_eq_two.symm),
    orbit_succ f (s z) z0 o1 (by show (1 : Ordinal.{0}) = 0 + 1; simp),
    orbit_zero f (s z) z0 rfl] at le
  rw [h2.2.2.2.2 f z]
  exact le

theorem next_ge_pow (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (c : CountableOrdinal) :
    (ω : Ordinal.{0}) ^ (c.val + 1) ≤ (fix pow c).val := by
  have h := fix_ge_stage_one h2 pow c
  rw [(h2.2.2.2.1 (s c)).2, h1.2.1 c] at h
  exact h

theorem omega_le_next_zero (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    (ω : Ordinal.{0}) ≤ (fix pow zeroValue).val := by
  have hn := next_ge_pow h1 h2 zeroValue
  have e : (ω : Ordinal.{0}) ^ (zeroValue.val + 1) = ω := by
    show (ω : Ordinal.{0}) ^ ((0 : Ordinal.{0}) + 1) = ω
    rw [zero_add, Ordinal.opow_one]
  rw [e] at hn
  exact hn

/-- For monotone inflationary `H ≥ Next`: `B_0 H 0 ≥ H 0 + H 0`. -/
theorem b0_zero_double (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (H : CountableOrdinal → CountableOrdinal) (hH : MonoInfl H)
    (hNext : ∀ x : CountableOrdinal, (fix pow x).val ≤ (H x).val) :
    (H zeroValue).val + (H zeroValue).val ≤ (towerValue fix 0 H zeroValue).val := by
  rw [b0_eq]
  have st : (orbit .base H zeroValue (orbit .base H zeroValue (s zeroValue))).val ≤
      (fix (fun α => orbit .base H zeroValue α) zeroValue).val :=
    fix_ge_stage_two h2 (fun α => orbit .base H zeroValue α) zeroValue
  have e1 : orbit .base H zeroValue (s zeroValue) = H zeroValue := by
    rw [orbit_succ H zeroValue zeroValue (s zeroValue) (h1.2.1 zeroValue),
      orbit_zero H zeroValue zeroValue rfl]
  obtain ⟨t, ht⟩ := countable_mk ((s zeroValue).val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt (s zeroValue)))
  have e2 : orbit .base H zeroValue t = H (H zeroValue) := by
    rw [orbit_succ H zeroValue (s zeroValue) t ht, e1]
  have ht2 : t.val < ω := by
    rw [ht, h1.2.1 zeroValue]
    show (0 : Ordinal.{0}) + 1 + 1 < ω
    rw [zero_add]
    exact one_add_one_lt_omega
  have c2 : t.val ≤ (H zeroValue).val :=
    ht2.le.trans ((omega_le_next_zero h1 h2).trans (hNext zeroValue))
  have m1 : (orbit .base H zeroValue t).val ≤ (orbit .base H zeroValue (H zeroValue)).val :=
    orbit_mono H zeroValue hH.2 c2
  rw [e2] at m1
  have m2 : (H zeroValue).val + (H zeroValue).val ≤ (H (H zeroValue)).val :=
    (add_self_le_opow _).trans ((next_ge_pow h1 h2 (H zeroValue)).trans (hNext (H zeroValue)))
  rw [e1] at st
  exact m2.trans (m1.trans st)

/-- `g (β+1) ≥ g β + g β` for `g β = (B_0^β Next) 0`. -/
theorem preLevel_double (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β β' : CountableOrdinal)
    (hβ : β'.val = β.val + 1) :
    (orbit (tier 1) (towerValue fix 0) (fix pow) β zeroValue).val +
      (orbit (tier 1) (towerValue fix 0) (fix pow) β zeroValue).val ≤
    (orbit (tier 1) (towerValue fix 0) (fix pow) β' zeroValue).val := by
  have eqs := orbitEquations (tier 1) (towerValue fix 0) (fix pow)
  have hNext : ∀ x : CountableOrdinal,
      (fix pow x).val ≤ (orbit (tier 1) (towerValue fix 0) (fix pow) β x).val := by
    intro x
    have h := (b0Orbit_mono h1 h2 β).2 zeroValue (ozl _) x
    rw [eqs.1 zeroValue rfl] at h
    exact h
  rw [eqs.2.1 β β' hβ]
  exact b0_zero_double h1 h2 (orbit (tier 1) (towerValue fix 0) (fix pow) β)
    (b0Orbit_mono h1 h2 β).1 hNext

theorem preLevel_id_le (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : ∀ y : CountableOrdinal,
    y.val ≤ (orbit (tier 1) (towerValue fix 0) (fix pow) y zeroValue).val := by
  refine countable_induction _ ?_ ?_ ?_
  · intro y h0
    exact le_of_eq_of_le h0 (ozl _)
  · intro y y' hy ih
    have pos : (0 : Ordinal.{0}) < (orbit (tier 1) (towerValue fix 0) (fix pow) y zeroValue).val :=
      (b0Orbit_mono h1 h2 y).1.2 zeroValue
    have one_le : (1 : Ordinal.{0}) ≤ (orbit (tier 1) (towerValue fix 0) (fix pow) y zeroValue).val := by
      have h := Order.add_one_le_of_lt pos
      rw [zero_add] at h
      exact h
    exact le_of_eq_of_le hy ((add_le_add ih one_le).trans (preLevel_double h1 h2 y y' hy))
  · intro l hl ih
    by_contra hlt
    rw [not_le] at hlt
    have hsucc : (orbit (tier 1) (towerValue fix 0) (fix pow) l zeroValue).val + 1 < l.val :=
      hl.add_one_lt hlt
    obtain ⟨e1, he1⟩ := countable_mk _ (hsucc.trans (countable_val_lt l))
    have e1lt : e1.val < l.val := by rw [he1]; exact hsucc
    have a := ih e1 e1lt
    rw [he1] at a
    have b := (b0Orbit_mono h1 h2 l).2 e1 e1lt.le zeroValue
    exact absurd (a.trans b) (not_le.2 (Order.lt_add_one_iff.2 le_rfl))

theorem veblen_double (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (y : CountableOrdinal) :
    y.val + y.val ≤ (veblenValue fix pow y).val := by
  rw [veblen_eq_fix]
  have a : (orbit (tier 1) (towerValue fix 0) (fix pow) (s y) zeroValue).val ≤
      (fix (fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue) y).val :=
    fix_ge_stage_one h2 (fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue) y
  have b := preLevel_double h1 h2 y (s y) (h1.2.1 y)
  exact (add_le_add (preLevel_id_le h1 h2 y) (preLevel_id_le h1 h2 y)).trans (b.trans a)

theorem omega_le_veblen (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (y : CountableOrdinal) :
    (ω : Ordinal.{0}) ≤ (veblenValue fix pow y).val := by
  have eqs := orbitEquations (tier 1) (towerValue fix 0) (fix pow)
  have a : (orbit (tier 1) (towerValue fix 0) (fix pow) (s y) zeroValue).val ≤
      (fix (fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue) y).val :=
    fix_ge_stage_one h2 (fun α => orbit (tier 1) (towerValue fix 0) (fix pow) α zeroValue) y
  have b := (b0Orbit_mono h1 h2 (s y)).2 zeroValue (ozl _) zeroValue
  rw [eqs.1 zeroValue rfl] at b
  rw [veblen_eq_fix]
  exact (omega_le_next_zero h1 h2).trans (b.trans a)

theorem veblen_infl (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : Inflationary (veblenValue fix pow) :=
  (veblenInflationary Z s add mul w one pow fix h1 h2).1

theorem base_gt_one (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : 1 < (baseValue fix pow w).val :=
  (veblenInflationary Z s add mul w one pow fix h1 h2).2

theorem level_ge_veblen (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β x : CountableOrdinal) :
    (veblenValue fix pow x).val ≤ (level fix pow β x).val := by
  have h := level_mono_index h1 h2 zeroValue β (ozl _) x
  rw [level_zero_eq zeroValue rfl] at h
  exact h

theorem level_double (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β x : CountableOrdinal) :
    x.val + x.val ≤ (level fix pow β x).val :=
  (veblen_double h1 h2 x).trans (level_ge_veblen h1 h2 β x)

/-! Positive fixed points of `E_β`. -/

theorem enumFix_gt_omega (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β κ : CountableOrdinal)
    (hκ : levelEnum fix pow β κ = κ) (hpos : 0 < κ.val) : (ω : Ordinal.{0}) < κ.val := by
  have hm := level_monoInfl h1 h2 β
  obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
  have e1 : levelEnum fix pow β o1 = level fix pow β zeroValue := by
    rw [lvEnum_succ β zeroValue o1 (ho1.trans (zero_add (1 : Ordinal.{0})).symm),
      lvEnum_zero β zeroValue rfl]
  have hω : (ω : Ordinal.{0}) ≤ (level fix pow β zeroValue).val :=
    (omega_le_veblen h1 h2 zeroValue).trans (level_ge_veblen h1 h2 β zeroValue)
  have one_le : o1.val ≤ κ.val := by
    rw [ho1]
    have h := Order.add_one_le_of_lt hpos
    rw [zero_add] at h
    exact h
  have a := lvEnum_mono h1 h2 β o1 κ one_le
  rw [e1, hκ] at a
  obtain ⟨o2, ho2⟩ := countable_mk (o1.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt o1))
  have two_le : o2.val ≤ κ.val := by
    rw [ho2, ho1]
    exact one_add_one_lt_omega.le.trans (hω.trans a)
  have b := lvEnum_mono h1 h2 β o2 κ two_le
  rw [lvEnum_succ β o1 o2 ho2, e1, hκ] at b
  exact hω.trans_lt ((hm.2 (level fix pow β zeroValue)).trans_le b)

theorem enumFix_limit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β κ : CountableOrdinal)
    (hκ : levelEnum fix pow β κ = κ) (hpos : 0 < κ.val) : Order.IsSuccLimit κ.val := by
  rcases countable_cases κ with h0 | ⟨c, hc⟩ | hl
  · exact absurd hpos (by rw [h0]; exact lt_irrefl _)
  · exfalso
    have big := enumFix_gt_omega h1 h2 β κ hκ hpos
    have a := level_double h1 h2 β (levelEnum fix pow β c)
    rw [← lvEnum_succ β c κ hc, hκ] at a
    have b : c.val + c.val ≤ c.val + 1 := by
      rw [← hc]
      exact (add_le_add (lvEnum_id_le h1 h2 β c) (lvEnum_id_le h1 h2 β c)).trans a
    have c1 : c.val ≤ 1 := (add_le_add_iff_left c.val).1 b
    have small : κ.val ≤ 1 + 1 := by
      rw [hc]
      exact add_le_add c1 le_rfl
    exact absurd (big.trans_le small) (not_lt.2 one_add_one_lt_omega.le)
  · exact hl

theorem enumFix_closed_level (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β κ : CountableOrdinal)
    (hκ : levelEnum fix pow β κ = κ) (hpos : 0 < κ.val) (y : CountableOrdinal)
    (hy : y.val < κ.val) : (level fix pow β y).val < κ.val := by
  have hl := enumFix_limit h1 h2 β κ hκ hpos
  have hm := level_monoInfl h1 h2 β
  have hy' : y.val < (orbit .base (level fix pow β) zeroValue κ).val :=
    lt_of_lt_of_eq hy (congrArg Subtype.val hκ).symm
  obtain ⟨a, ha, hya⟩ := lt_orbit_limit (level fix pow β) zeroValue κ hl y.val hy'
  obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1) ((hl.add_one_lt ha).trans (countable_val_lt κ))
  have s1 : (level fix pow β y).val ≤ (levelEnum fix pow β a1).val := by
    rw [lvEnum_succ β a a1 ha1]
    exact hm.1 y (levelEnum fix pow β a) hya.le
  have s2 : (levelEnum fix pow β a1).val < (levelEnum fix pow β κ).val :=
    lvEnum_strict h1 h2 β a1 κ (by rw [ha1]; exact hl.add_one_lt ha)
  rw [hκ] at s2
  exact s1.trans_lt s2

theorem enumFix_add_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β κ : CountableOrdinal)
    (hκ : levelEnum fix pow β κ = κ) (hpos : 0 < κ.val) (y b : CountableOrdinal)
    (hy : y.val < κ.val) (hb : b.val < κ.val) : y.val + b.val < κ.val := by
  rcases le_total y.val b.val with h | h
  · exact ((add_le_add h le_rfl).trans (level_double h1 h2 β b)).trans_lt
      (enumFix_closed_level h1 h2 β κ hκ hpos b hb)
  · exact ((add_le_add le_rfl h).trans (level_double h1 h2 β y)).trans_lt
      (enumFix_closed_level h1 h2 β κ hκ hpos y hy)

theorem enumFix_orbit_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β κ : CountableOrdinal)
    (hκ : levelEnum fix pow β κ = κ) (hpos : 0 < κ.val) (y b : CountableOrdinal)
    (hy : y.val < κ.val) (hb : b.val < κ.val) :
    (orbit .base (level fix pow β) y b).val < κ.val := by
  have hm := level_monoInfl h1 h2 β
  have hsum := enumFix_add_closed h1 h2 β κ hκ hpos y b hy hb
  obtain ⟨yb, hyb⟩ := countable_mk (y.val + b.val) (hsum.trans (countable_val_lt κ))
  have s1 : (orbit .base (level fix pow β) y b).val ≤
      (orbit .base (level fix pow β) (levelEnum fix pow β y) b).val :=
    orbit_start_mono (level fix pow β) hm.1 y (levelEnum fix pow β y) (lvEnum_id_le h1 h2 β y) b
  have s2 : (orbit .base (level fix pow β) (levelEnum fix pow β y) b).val ≤
      (levelEnum fix pow β yb).val :=
    orbit_compose_le (level fix pow β) hm zeroValue y b yb hyb
  have s3 : (levelEnum fix pow β yb).val < (levelEnum fix pow β κ).val :=
    lvEnum_strict h1 h2 β yb κ (by rw [hyb]; exact hsum)
  rw [hκ] at s3
  exact (s1.trans s2).trans_lt s3

/-! Strict T3 and `L = (β ↦ D β 0)`. -/

theorem level_lt_succ (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (β β' : CountableOrdinal)
    (hβ : β'.val = β.val + 1) (x : CountableOrdinal) :
    (level fix pow β x).val < (level fix pow β' x).val := by
  obtain ⟨hfix, hx, -⟩ := level_step h1 h2 β β' hβ x
  exact enumFix_closed_level h1 h2 β (level fix pow β' x) hfix ((ozl _).trans_lt hx) x hx

theorem levelZero_strict (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (α β : CountableOrdinal)
    (h : α.val < β.val) :
    (level fix pow α zeroValue).val < (level fix pow β zeroValue).val := by
  obtain ⟨α1, hα1⟩ := countable_mk (α.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt α))
  exact (level_lt_succ h1 h2 α α1 hα1 zeroValue).trans_le
    (level_mono_index h1 h2 α1 β (by rw [hα1]; exact Order.add_one_le_of_lt h) zeroValue)

theorem levelZero_id_le (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ α : CountableOrdinal, α.val ≤ (level fix pow α zeroValue).val := by
  refine countable_strong_induction _ (fun α ih => ?_)
  by_contra hlt
  rw [not_le] at hlt
  have a := ih (level fix pow α zeroValue) hlt
  have b := levelZero_strict h1 h2 (level fix pow α zeroValue) α hlt
  exact absurd a (not_le.2 b)

/-- If `Θ > 1` is closed under `L` on `[1, Θ)`, then `L` has a fixed point in `[1, Θ]`. -/
theorem levelZero_closed_fix (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (Θ : CountableOrdinal) (hΘ : 1 < Θ.val)
    (H : ∀ e : CountableOrdinal, 1 ≤ e.val → e.val < Θ.val →
      (level fix pow e zeroValue).val < Θ.val) :
    ∃ θ : CountableOrdinal, 1 ≤ θ.val ∧ θ.val ≤ Θ.val ∧ level fix pow θ zeroValue = θ := by
  rcases countable_cases Θ with h0 | ⟨c, hc⟩ | hl
  · exact absurd hΘ (by rw [h0]; exact not_lt.2 zero_le_one)
  · have hcΘ : c.val < Θ.val := by rw [hc]; exact Order.lt_add_one_iff.2 le_rfl
    have c1 : 1 ≤ c.val := by
      rw [hc] at hΘ
      exact Order.lt_add_one_iff.1 hΘ
    have a := H c c1 hcΘ
    rw [hc] at a
    exact ⟨c, c1, hcΘ.le,
      Subtype.ext (le_antisymm (Order.lt_add_one_iff.1 a) (levelZero_id_le h1 h2 c))⟩
  · refine ⟨Θ, hΘ.le, le_rfl, Subtype.ext (le_antisymm ?_ (levelZero_id_le h1 h2 Θ))⟩
    refine level_limit_le Θ hl zeroValue _ (fun β hβ => ?_)
    obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
    have o1Θ : o1.val < Θ.val := by rw [ho1]; exact hΘ
    rcases le_total β.val o1.val with h | h
    · exact ((level_mono_index h1 h2 β o1 h zeroValue).trans_lt (H o1 (le_of_eq ho1.symm) o1Θ)).le
    · exact (H β ((le_of_eq ho1.symm).trans h) hβ).le

/-! `D e Γ_0 = D e 0` for `e ≥ 1`. -/

theorem base_lt_level (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (e : CountableOrdinal) (he : 1 ≤ e.val) :
    (baseValue fix pow w).val < (level fix pow e zeroValue).val := by
  obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
  obtain ⟨hfix, hx, -⟩ := level_step h1 h2 zeroValue o1
    (ho1.trans (zero_add (1 : Ordinal.{0})).symm) zeroValue
  have hpos : 0 < (level fix pow o1 zeroValue).val := hx
  have big := enumFix_gt_omega h1 h2 zeroValue _ hfix hpos
  have cl := enumFix_closed_level h1 h2 zeroValue _ hfix hpos w (by rw [h2.1]; exact big)
  rw [level_zero_eq zeroValue rfl] at cl
  exact cl.trans_le (level_mono_index h1 h2 o1 e (by rw [ho1]; exact he) zeroValue)

theorem level_restart (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ e : CountableOrdinal, 1 ≤ e.val → ∀ y : CountableOrdinal,
      y.val < (level fix pow e zeroValue).val →
      (level fix pow e y).val ≤ (level fix pow e zeroValue).val := by
  refine countable_induction _ ?_ ?_ ?_
  · intro e h0 h1e
    rw [h0] at h1e
    exact absurd h1e (not_le.2 zero_lt_one)
  · intro e' e he _ _ y hy
    obtain ⟨hfix, -, -⟩ := level_step h1 h2 e' e he zeroValue
    exact (level_step h1 h2 e' e he y).2.2 _ hy hfix
  · intro l hl ih _ y hy
    obtain ⟨β, hβ, hyβ⟩ := lt_level_limit l hl zeroValue y.val hy
    refine level_limit_le l hl y _ (fun β' hβ' => ?_)
    have hmax : max (max β'.val β.val) 1 < l.val :=
      max_lt (max_lt hβ' hβ) (Ordinal.one_lt_of_isSuccLimit hl)
    obtain ⟨m, hm⟩ := countable_mk (max (max β'.val β.val) 1) (hmax.trans (countable_val_lt l))
    have hml : m.val < l.val := by rw [hm]; exact hmax
    have a := level_mono_index h1 h2 β' m
      (by rw [hm]; exact (le_max_left _ _).trans (le_max_left _ _)) y
    have hyβm : y.val < (level fix pow m zeroValue).val :=
      hyβ.trans_le (level_mono_index h1 h2 β m
        (by rw [hm]; exact (le_max_right _ _).trans (le_max_left _ _)) zeroValue)
    have b := ih m hml (by rw [hm]; exact le_max_right _ _) y hyβm
    exact (a.trans b).trans (level_mono_index h1 h2 m l hml.le zeroValue)

theorem level_base_eq (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (e : CountableOrdinal) (he : 1 ≤ e.val) :
    level fix pow e (baseValue fix pow w) = level fix pow e zeroValue :=
  Subtype.ext (le_antisymm
    (level_restart h1 h2 e he (baseValue fix pow w) (base_lt_level h1 h2 e he))
    ((level_monoInfl h1 h2 e).1 zeroValue (baseValue fix pow w) (ozl _)))

end

theorem veblenDoubling : VeblenDoubling := by
  intro Z s add mul w one pow fix h1 h2 y
  exact veblen_double h1 h2 y

theorem levelStrict : LevelStrict := by
  intro Z s add mul w one pow fix h1 h2
  exact ⟨fun β β' hβ x => level_lt_succ h1 h2 β β' hβ x,
    fun α β h => levelZero_strict h1 h2 α β h, fun α => levelZero_id_le h1 h2 α⟩

theorem levelBaseRestart : LevelBaseRestart := by
  intro Z s add mul w one pow fix h1 h2 e he
  exact level_base_eq h1 h2 e he

#print axioms veblenDoubling
#print axioms levelStrict
#print axioms levelBaseRestart
#print axioms levelZero_closed_fix
#print axioms enumFix_orbit_closed

end LogicLineages.PersistentMarking.ActualCalibrationThree
