module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformWeightProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelTwoProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelOneProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsLimitProof
public import LogicLineages.NativeModule.PersistentMarking.ActualTowerIndexProof

@[expose] public section

/-! Root's per-level statements at every level: the tower environment is weighted (all weights 0),
the level orbit `B_{n+1}^e B_n` has weight `e`, so applied down the tower environment it is a step
at `towerIndex (n+2) e`; `PsiTowerLevelAt (n+2)` then follows from the step at the empty context as
at level 2 (`psiO_tower_two`), and `LevelFactsAt (n+2)` from the good-family facts. Level 1 is
`ActualCalibrationLevelOneProof`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationUniform
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationStep ActualCalibrationLevels ActualTowerIndex Paper16RemainingOrdinalTargets
open scoped Ordinal

/-! The tower indices. -/

theorem towerIndex_shift : ∀ (k : Nat) (σ : Ordinal.{0}),
    towerIndex k (omegaIndex ^ σ) = towerIndex (k + 1) σ := by
  intro k
  induction k with
  | zero =>
    intro σ
    rfl
  | succ k ih =>
    intro σ
    show omegaIndex ^ towerIndex k (omegaIndex ^ σ) = omegaIndex ^ towerIndex (k + 1) σ
    rw [ih σ]

theorem towerIndex_lt : ∀ (k : Nat) (a b : Ordinal.{0}), a < b →
    towerIndex k a < towerIndex k b := by
  intro k
  induction k with
  | zero =>
    intro a b h
    exact h
  | succ k ih =>
    intro a b h
    show omegaIndex ^ towerIndex k a < omegaIndex ^ towerIndex k b
    exact (Ordinal.opow_lt_opow_iff_right one_lt_index).2 (ih a b h)

theorem expDown_zero : ∀ (k : Nat) (σ : Ordinal.{0}),
    expDown k (fun _ => 0) σ = towerIndex k σ := by
  intro k
  induction k with
  | zero =>
    intro σ
    rfl
  | succ k ih =>
    intro σ
    show expDown k (fun _ => 0) ((0 : Ordinal.{0}) + omegaIndex ^ σ) = towerIndex (k + 1) σ
    rw [zero_add, ih (omegaIndex ^ σ), towerIndex_shift]

theorem condDown_zero : ∀ (k : Nat) (σ : Ordinal.{0}),
    omegaIndex ^ towerIndex k σ < endpoint → CondDown k (fun _ => 0) σ := by
  intro k
  induction k with
  | zero =>
    intro σ h
    exact h
  | succ k ih =>
    intro σ h
    have hσ : omegaIndex ^ σ < endpoint := by
      have hle := le_expDown (k + 1) (fun _ => 0) σ
      rw [expDown_zero] at hle
      exact lt_of_le_of_lt (Ordinal.opow_le_opow_right omegaIndex_pos hle) h
    show ExpSep (0 : Ordinal.{0}) σ ∧
      CondDown k (fun _ => 0) ((0 : Ordinal.{0}) + omegaIndex ^ σ)
    refine ⟨expSep_zero σ hσ, ?_⟩
    rw [zero_add]
    refine ih (omegaIndex ^ σ) ?_
    rw [towerIndex_shift]
    exact h

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

/-- Every slot of the tower environment has weight 0. -/
theorem towerEnv_weight (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (k : Nat) :
    WeightF fix pow w k 0 (towerEnv fix pow (k + 1)) := by
  cases k with
  | zero =>
    have gN : GoodFn fix pow w (veblenValue fix pow) := goodVeblen h1 h2
    have sb := stepBase Z s add mul w one pow fix h1 h2
    refine ⟨fun xs _ => ⟨gN, trivial⟩, fun xs ss _ _ => ?_⟩
    show StepUp fix pow w (omegaIndex ^ (0 : Ordinal.{0})) (veblenValue fix pow) ∧
      StepLow fix pow w (omegaIndex ^ (0 : Ordinal.{0})) (veblenValue fix pow)
    rw [Ordinal.opow_zero]
    exact sb
  | succ j =>
    exact towerWeight Z s add mul w one pow fix h1 h2 j

theorem towerEnv_wEnv (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ k : Nat, WEnv fix pow w k (towerEnv fix pow) (fun _ => 0) := by
  intro k
  induction k with
  | zero => exact trivial
  | succ k ih =>
    show WEnv fix pow w k (towerEnv fix pow) (fun _ => 0) ∧
      WeightAt fix pow w k (WEnv fix pow w k) (0 : Ordinal.{0}) (towerEnv fix pow (k + 1))
    exact ⟨ih, towerEnv_weight h1 h2 k⟩

/-- A good object applied down a good environment lies above `B_0` of slot 1. -/
theorem good_above_b0 (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ (k : Nat) (F : Value (tier (k + 2))) (xs : Env), GoodF fix pow w (k + 1) F →
      GoodEnv fix pow w (k + 1) xs → ∀ x : CountableOrdinal,
        (towerValue fix 0 (xs 1) x).val ≤ (appDown (k + 1) F xs x).val := by
  intro k
  induction k with
  | zero =>
    intro F xs hF hxs x
    have d : ∀ x : CountableOrdinal,
        (towerValue fix 0 (appDown 0 (xs 1) xs) x).val ≤ (appDown 1 F xs x).val := (hF xs hxs).2
    exact d x
  | succ k ih =>
    intro F xs hF hxs x
    have d : ∀ x : CountableOrdinal,
        (towerValue fix 0 (appDown (k + 1) (xs (k + 2)) xs) x).val ≤
          (appDown (k + 2) F xs x).val := (hF xs hxs).2
    have hxs' : GoodEnv fix pow w (k + 1) xs ∧
        GoodAt fix pow w (k + 1) (GoodEnv fix pow w (k + 1)) (xs (k + 2)) := hxs
    have gK : GoodFn fix pow w (appDown (k + 1) (xs (k + 2)) xs) := (hxs'.2 xs hxs'.1).1
    exact ((ih (xs (k + 2)) xs hxs'.2 hxs'.1 x).trans
      ((b0_monoInfl h1 h2 (appDown (k + 1) (xs (k + 2)) xs) gK.1).2 x)).trans (d x)

/-- `B_{k+1} Ψ` applied down is `fix` of the zero-diagonal of the applied-down orbit of `Ψ`. -/
theorem appDown_tower_app (k : Nat) (Ψ : Value (tier (k + 2))) (xs : Env) :
    appDown (k + 1) (towerValue fix (k + 1) Ψ) xs =
      fix (fun a => appDown k (orbit (tier (k + 1)) Ψ (xs (k + 1)) a) xs zeroValue) := by
  have e2 : ∀ a : CountableOrdinal,
      appDown k (orbit (tier (k + 1)) (Function.update xs (k + 2) Ψ (k + 2))
        (Function.update xs (k + 2) Ψ (k + 1)) a) (Function.update xs (k + 2) Ψ) zeroValue =
      appDown k (orbit (tier (k + 1)) Ψ (xs (k + 1)) a) xs zeroValue := by
    intro a
    rw [env_update_self, env_update_ne xs (k + 2) (k + 1) Ψ (by omega),
      appDown_congr k (orbit (tier (k + 1)) Ψ (xs (k + 1)) a) (Function.update xs (k + 2) Ψ) xs
        (fun j _ hj => env_update_ne xs (k + 2) j Ψ (by omega))]
  exact (appDown_update (k + 1) (towerValue fix (k + 1)) Ψ xs).symm.trans
    ((appDown_tower_succ fix k (Function.update xs (k + 2) Ψ)).trans
      (congrArg (fun g : CountableOrdinal → CountableOrdinal => fix g) (funext e2)))

end

/-- The level orbit applied down the tower environment. -/
noncomputable def levelFn (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (n : Nat) (e : CountableOrdinal) :
    CountableOrdinal → CountableOrdinal :=
  appDown (n + 1) (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e)
    (towerEnv fix pow)

theorem levelDiagonal_eq (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (n : Nat) (e : CountableOrdinal) :
    levelDiagonal fix pow (n + 2) e = levelFn fix pow n e zeroValue :=
  semDown_appDown (n + 1)
    (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e) (towerEnv fix pow)

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem levelFn_family (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (n : Nat) :
    GoodFamily fix pow w (levelFn fix pow n) :=
  orbit_family h1 h2 (n + 1) (towerValue fix (n + 1)) (towerValue fix n)
    (towerGood Z s add mul w one pow fix h1 h2 (n + 1))
    (towerGood Z s add mul w one pow fix h1 h2 n) (towerEnv fix pow)
    (wEnv_good (n + 1) (towerEnv fix pow) (fun _ => 0) (towerEnv_wEnv h1 h2 (n + 1)))

/-- `Γ_0 < levelFn n e 0`. -/
theorem base_lt_levelFn (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (n : Nat) (e : CountableOrdinal) :
    (baseValue fix pow w).val < (levelFn fix pow n e zeroValue).val := by
  have og := orbitGood Z s add mul w one pow fix h1 h2 (n + 1) (towerValue fix (n + 1))
    (towerValue fix n) (towerGood Z s add mul w one pow fix h1 h2 (n + 1))
    (towerGood Z s add mul w one pow fix h1 h2 n) e
  have h := good_above_b0 h1 h2 n
    (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e) (towerEnv fix pow) og
    (wEnv_good (n + 1) (towerEnv fix pow) (fun _ => 0) (towerEnv_wEnv h1 h2 (n + 1))) zeroValue
  exact lt_of_lt_of_le (base_lt_b0 h1 h2) h

/-- For `e ≥ 1` the level function restarts below its value at 0. -/
theorem levelFn_restart (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (n : Nat) :
    ∀ e : CountableOrdinal, 1 ≤ e.val → ∀ y : CountableOrdinal,
      y.val < (levelFn fix pow n e zeroValue).val →
      (levelFn fix pow n e y).val ≤ (levelFn fix pow n e zeroValue).val := by
  have fam := levelFn_family (w := w) h1 h2 n
  have tgs := towerGood Z s add mul w one pow fix h1 h2
  have gE := wEnv_good (n + 1) (towerEnv fix pow) (fun _ => 0) (towerEnv_wEnv (w := w) h1 h2 (n + 1))
  have gE' : GoodEnv fix pow w n (towerEnv fix pow) ∧
      GoodAt fix pow w n (GoodEnv fix pow w n) (towerEnv fix pow (n + 1)) := gE
  have eqs := orbitEquations (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n)
  refine countable_induction _ ?_ ?_ ?_
  · intro e h0 h1e
    rw [h0] at h1e
    exact absurd h1e (not_le.2 zero_lt_one)
  · intro e' e he _ _ y hy
    have og := orbitGood Z s add mul w one pow fix h1 h2 (n + 1) (towerValue fix (n + 1))
      (towerValue fix n) (tgs (n + 1)) (tgs n) e'
    have famK := orbit_family h1 h2 n
      (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e')
      (towerEnv fix pow (n + 1)) og gE'.2 (towerEnv fix pow) gE'.1
    have eV : levelFn fix pow n e =
        fix (fun a => appDown n (orbit (tier (n + 1))
          (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e')
          (towerEnv fix pow (n + 1)) a) (towerEnv fix pow) zeroValue) := by
      show appDown (n + 1) (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e)
        (towerEnv fix pow) = _
      rw [eqs.2.1 e' e he]
      exact appDown_tower_app n
        (orbit (tier (n + 2)) (towerValue fix (n + 1)) (towerValue fix n) e') (towerEnv fix pow)
    rw [eV] at hy ⊢
    exact (fam_spec h1 h2 _ famK y).2.2 _ hy (fam_spec h1 h2 _ famK zeroValue).1
  · intro l hl ih _ y hy
    obtain ⟨i, hil, hi⟩ := fam_lt_limit (levelFn fix pow n) fam l hl zeroValue y.val hy
    refine fam_limit_le (levelFn fix pow n) fam l hl y _ (fun j hj => ?_)
    have hmax : max (max j.val i.val) 1 < l.val :=
      max_lt (max_lt hj hil) (Ordinal.one_lt_of_isSuccLimit hl)
    obtain ⟨m, hm⟩ := countable_mk (max (max j.val i.val) 1) (hmax.trans (countable_val_lt l))
    have hml : m.val < l.val := by rw [hm]; exact hmax
    have hjm : j.val ≤ m.val := by
      rw [hm]
      exact (le_max_left j.val i.val).trans (le_max_left _ _)
    have him : i.val ≤ m.val := by
      rw [hm]
      exact (le_max_right j.val i.val).trans (le_max_left _ _)
    have a := fam_mono h1 h2 (levelFn fix pow n) fam m j hjm y
    have hyim : y.val < (levelFn fix pow n m zeroValue).val :=
      lt_of_lt_of_le hi (fam_mono h1 h2 (levelFn fix pow n) fam m i him zeroValue)
    have b := ih m hml (by rw [hm]; exact le_max_right _ _) y hyim
    exact (a.trans b).trans (fam_mono h1 h2 (levelFn fix pow n) fam l m hml.le zeroValue)

/-- The collapse along `towerIndex (n+2) e`, in `psiO` form. -/
theorem psiO_tower_level (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (n : Nat) :
    ∀ e : CountableOrdinal, 1 ≤ e.val →
      (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val → levelFn fix pow n θ zeroValue ≠ θ) →
      psiO fix pow w (towerIndex (n + 2) e.val) = (levelFn fix pow n e zeroValue).val := by
  have fam := levelFn_family (w := w) h1 h2 n
  obtain ⟨below, normLe, -⟩ := ActualTowerIndexProof.exact_TowerIndexFacts (n + 2)
  have hbnd : ∀ e : CountableOrdinal, towerIndex (n + 2) e.val < endpoint := fun e =>
    (below e.val (countable_val_lt e)).trans (exact_BelowEndpoint (n + 2 + 2))
  have hb1 : omegaIndex ^ ((0 : Ordinal.{0}) + 1) ≤ endpoint := by
    rw [zero_add]
    exact (Ordinal.opow_le_opow_right omegaIndex_pos one_lt_index.le).trans top_le_endpoint
  have ow := orbitWeight Z s add mul w one pow fix h1 h2 (n + 1) (towerValue fix (n + 1))
    (towerValue fix n) 0 0 (towerWeight Z s add mul w one pow fix h1 h2 (n + 1))
    (towerWeight Z s add mul w one pow fix h1 h2 n) (nsep_zero _) hb1
  have stepAt : ∀ e : CountableOrdinal,
      StepUp fix pow w (towerIndex (n + 2) e.val) (levelFn fix pow n e) ∧
      StepLow fix pow w (towerIndex (n + 2) e.val) (levelFn fix pow n e) := by
    intro e
    have owe := ow e
    rw [Ordinal.opow_zero, one_mul, zero_add] at owe
    have hΛ : omegaIndex ^ towerIndex (n + 1) e.val < endpoint := hbnd e
    have st := owe.2 (towerEnv fix pow) (fun _ => 0) (towerEnv_wEnv h1 h2 (n + 1))
      (condDown_zero (n + 1) e.val hΛ)
    rw [expDown_zero] at st
    exact st
  have strictD : ∀ a b : CountableOrdinal, a.val < b.val →
      (levelFn fix pow n a zeroValue).val < (levelFn fix pow n b zeroValue).val :=
    fun a b hab => fam_lt h1 h2 (levelFn fix pow n) fam a b hab zeroValue
  have limD : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ b : Ordinal.{0},
      (∀ a : CountableOrdinal, a.val < l.val → (levelFn fix pow n a zeroValue).val ≤ b) →
      (levelFn fix pow n l zeroValue).val ≤ b :=
    fun l hl b Hb => fam_limit_le (levelFn fix pow n) fam l hl zeroValue b Hb
  refine countable_strong_induction _ (fun e ih he1 hnofix => ?_)
  have hb := hbnd e
  have hend : towerIndex (n + 2) e.val ≤ endpoint := hb.le
  have stp := stepAt e
  have ctx : StepContext 0 (towerIndex (n + 2) e.val) := by
    refine ⟨?_, fun τ _ => ?_⟩
    · rw [zero_add]
      exact hend
    · rw [zero_add, cnorm_zero]
      exact (max_eq_right (ozl _)).symm
  have up := stp.1 0 (baseValue fix pow w) ctx crit_base (psiO_zero_le h1 h2)
  rw [zero_add] at up
  have hΓ := base_lt_levelFn (w := w) h1 h2 n e
  have up' : psiO fix pow w (towerIndex (n + 2) e.val) ≤ (levelFn fix pow n e zeroValue).val :=
    up.trans (levelFn_restart h1 h2 n e he1 (baseValue fix pow w) hΓ)
  have nTop : coefficientNorm (towerIndex (n + 2) e.val) ≤ e.val :=
    normLe e.val he1 (countable_val_lt e)
  have act : e.val < psiO fix pow w (towerIndex (n + 2) e.val) := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨Θ, hΘ⟩ := crit_val (psiO_crit (w := w) h1 h2 hend)
    have hΘ1 : 1 < Θ.val := by
      rw [hΘ]
      exact psiO_gt_one h1 h2 hend
    have hΘe : Θ.val ≤ e.val := by
      rw [hΘ]
      exact hcon
    have H : ∀ e' : CountableOrdinal, 1 ≤ e'.val → e'.val < Θ.val →
        (levelFn fix pow n e' zeroValue).val < Θ.val := by
      intro e' he'1 he'Θ
      have he'e : e'.val < e.val := lt_of_lt_of_le he'Θ hΘe
      have hpow : towerIndex (n + 2) e'.val < towerIndex (n + 2) e.val :=
        towerIndex_lt (n + 2) e'.val e.val he'e
      have hn' : coefficientNorm (towerIndex (n + 2) e'.val) ≤ e'.val :=
        normLe e'.val he'1 (countable_val_lt e')
      have cl := psiO_closure (w := w) h1 h2 hend hpow
        (lt_of_le_of_lt hn' (lt_of_lt_of_eq he'Θ hΘ))
      rw [ih e' he'e he'1 (fun θ' a b => hnofix θ' a (b.trans he'e.le)), ← hΘ] at cl
      exact cl
    obtain ⟨θ, hθ1, hθΘ, hfix⟩ := diag_closed_fix
      (fun a => levelFn fix pow n a zeroValue) strictD limD Θ hΘ1 H
    exact hnofix θ hθ1 (hθΘ.trans hΘe) hfix
  have low := stp.2 0 zeroValue ctx
    (by rw [cnorm_zero, zero_add]; exact lt_of_le_of_lt (ozl _) act)
    (by rw [zero_add]; exact lt_of_le_of_lt nTop act) (ozl _)
  rw [zero_add] at low
  exact le_antisymm up' low

end

theorem allLevels : AllLevels := by
  intro Z s add mul w one pow fix h1 h2 l hl
  match l, hl with
  | 0, h0 => exact absurd h0 (by omega)
  | 1, _ =>
    exact ⟨levelFactsAt_one Z s add mul w one pow fix h1 h2,
      psiTowerLevelAt_one Z s add mul w one pow fix h1 h2⟩
  | n + 2, _ =>
    have fam := levelFn_family (w := w) h1 h2 n
    refine ⟨⟨fun α β hαβ => ?_, fun e _ => ?_, fun lim hlim => ?_⟩, ?_⟩
    · rw [levelDiagonal_eq fix pow n α, levelDiagonal_eq fix pow n β]
      exact fam_lt h1 h2 (levelFn fix pow n) fam α β hαβ zeroValue
    · rw [levelDiagonal_eq fix pow n e]
      exact base_lt_levelFn h1 h2 n e
    · exact ActualCalibrationLevelsLimitProof.exact_LevelDiagonalLimit fix pow (n + 2) lim hlim
    · intro e he1 hnofix h
      have h' : towerIndex (n + 2) e.val ≤ endpoint := h
      have r := psiO_tower_level (w := w) h1 h2 n e he1
        (fun θ hθ1 hθe hfix => hnofix θ hθ1 hθe ((levelDiagonal_eq fix pow n θ).trans hfix))
      rw [psiO_eq h'] at r
      rw [levelDiagonal_eq fix pow n e]
      exact r

#print axioms allLevels

end LogicLineages.PersistentMarking.ActualCalibrationUniform
