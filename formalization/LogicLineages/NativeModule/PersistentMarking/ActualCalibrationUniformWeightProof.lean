module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformNormProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformGoodProof

@[expose] public section

/-! Weights at every type: weighted environments, closure of weights under application
(`weightF_app`: weight `σ` applied to weight `ε` has weight `ε + Ω^σ`), `orbitWeight` (stage `a` of
the orbit has weight `σ' + Ω^σ·a`; limits by `stepLimit`), and `towerWeight`: every `B_m` has
weight `0` (`m = 0`: `stepSuccessor`; `m ≥ 1`: `stepDiagonal` on the applied-down orbit). -/

namespace LogicLineages.PersistentMarking.ActualCalibrationUniform
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationStep
open scoped Ordinal

/-! Weighted environments. -/

theorem ss_update_ne (ss : Nat → Ordinal.{0}) (k j : Nat) (ε : Ordinal.{0}) (h : j ≠ k) :
    Function.update ss k ε j = ss j :=
  Function.update_of_ne h _ ss

theorem ss_update_self (ss : Nat → Ordinal.{0}) (k : Nat) (ε : Ordinal.{0}) :
    Function.update ss k ε k = ε :=
  Function.update_self k ε ss

theorem expDown_congr : ∀ (k : Nat) (ss ts : Nat → Ordinal.{0}) (σ : Ordinal.{0}),
    (∀ j, 1 ≤ j → j ≤ k → ss j = ts j) → expDown k ss σ = expDown k ts σ := by
  intro k
  induction k with
  | zero =>
    intro ss ts σ _
    rfl
  | succ k ih =>
    intro ss ts σ h
    show expDown k ss (ss (k + 1) + omegaIndex ^ σ) = expDown k ts (ts (k + 1) + omegaIndex ^ σ)
    rw [h (k + 1) (by omega) le_rfl]
    exact ih ss ts _ (fun j h1 hj => h j h1 (by omega))

theorem condDown_congr : ∀ (k : Nat) (ss ts : Nat → Ordinal.{0}) (σ : Ordinal.{0}),
    (∀ j, 1 ≤ j → j ≤ k → ss j = ts j) → CondDown k ss σ → CondDown k ts σ := by
  intro k
  induction k with
  | zero =>
    intro ss ts σ _ h
    exact h
  | succ k ih =>
    intro ss ts σ h hc
    have hc' : ExpSep (ss (k + 1)) σ ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ σ) := hc
    rw [h (k + 1) (by omega) le_rfl] at hc'
    show ExpSep (ts (k + 1)) σ ∧ CondDown k ts (ts (k + 1) + omegaIndex ^ σ)
    exact ⟨hc'.1, ih ss ts _ (fun j h1 hj => h j h1 (by omega)) hc'.2⟩

theorem expDown_update (k : Nat) (ss : Nat → Ordinal.{0}) (ε σ : Ordinal.{0}) :
    expDown (k + 1) (Function.update ss (k + 1) ε) σ = expDown k ss (ε + omegaIndex ^ σ) := by
  show expDown k (Function.update ss (k + 1) ε)
    (Function.update ss (k + 1) ε (k + 1) + omegaIndex ^ σ) = expDown k ss (ε + omegaIndex ^ σ)
  rw [ss_update_self]
  exact expDown_congr k (Function.update ss (k + 1) ε) ss (ε + omegaIndex ^ σ)
    (fun j _ hj => ss_update_ne ss (k + 1) j ε (by omega))

theorem condDown_update (k : Nat) (ss : Nat → Ordinal.{0}) (ε σ : Ordinal.{0}) (hS : ExpSep ε σ)
    (hc : CondDown k ss (ε + omegaIndex ^ σ)) :
    CondDown (k + 1) (Function.update ss (k + 1) ε) σ := by
  show ExpSep (Function.update ss (k + 1) ε (k + 1)) σ ∧
    CondDown k (Function.update ss (k + 1) ε)
      (Function.update ss (k + 1) ε (k + 1) + omegaIndex ^ σ)
  rw [ss_update_self]
  exact ⟨hS, condDown_congr k ss (Function.update ss (k + 1) ε) (ε + omegaIndex ^ σ)
    (fun j _ hj => (ss_update_ne ss (k + 1) j ε (by omega)).symm) hc⟩

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem wEnv_congr : ∀ (k : Nat) (xs ys : Env) (ss ts : Nat → Ordinal.{0}),
    (∀ j, 1 ≤ j → j ≤ k → xs j = ys j) → (∀ j, 1 ≤ j → j ≤ k → ss j = ts j) →
    WEnv fix pow w k xs ss → WEnv fix pow w k ys ts := by
  intro k
  induction k with
  | zero =>
    intro xs ys ss ts _ _ _
    exact trivial
  | succ k ih =>
    intro xs ys ss ts hx hs h
    have h' : WEnv fix pow w k xs ss ∧
        WeightAt fix pow w k (WEnv fix pow w k) (ss (k + 1)) (xs (k + 1)) := h
    rw [hx (k + 1) (by omega) le_rfl, hs (k + 1) (by omega) le_rfl] at h'
    show WEnv fix pow w k ys ts ∧
      WeightAt fix pow w k (WEnv fix pow w k) (ts (k + 1)) (ys (k + 1))
    exact ⟨ih xs ys ss ts (fun j h1 hj => hx j h1 (by omega)) (fun j h1 hj => hs j h1 (by omega))
      h'.1, h'.2⟩

theorem wEnv_update (k : Nat) (xs : Env) (ss : Nat → Ordinal.{0}) (G : Value (tier (k + 1)))
    (ε : Ordinal.{0}) (hxs : WEnv fix pow w k xs ss) (hG : WeightF fix pow w k ε G) :
    WEnv fix pow w (k + 1) (Function.update xs (k + 1) G) (Function.update ss (k + 1) ε) := by
  show WEnv fix pow w k (Function.update xs (k + 1) G) (Function.update ss (k + 1) ε) ∧
    WeightAt fix pow w k (WEnv fix pow w k) (Function.update ss (k + 1) ε (k + 1))
      (Function.update xs (k + 1) G (k + 1))
  rw [ss_update_self, env_update_self]
  exact ⟨wEnv_congr k xs (Function.update xs (k + 1) G) ss (Function.update ss (k + 1) ε)
    (fun j _ hj => (env_update_ne xs (k + 1) j G (by omega)).symm)
    (fun j _ hj => (ss_update_ne ss (k + 1) j ε (by omega)).symm) hxs, hG⟩

theorem wEnv_good : ∀ (k : Nat) (xs : Env) (ss : Nat → Ordinal.{0}),
    WEnv fix pow w k xs ss → GoodEnv fix pow w k xs := by
  intro k
  induction k with
  | zero =>
    intro xs ss _
    exact trivial
  | succ k ih =>
    intro xs ss h
    have h' : WEnv fix pow w k xs ss ∧
        WeightAt fix pow w k (WEnv fix pow w k) (ss (k + 1)) (xs (k + 1)) := h
    show GoodEnv fix pow w k xs ∧ GoodAt fix pow w k (GoodEnv fix pow w k) (xs (k + 1))
    exact ⟨ih xs ss h'.1, h'.2.1⟩

/-- Weight `σ` applied to weight `ε` has weight `ε + Ω^σ`. -/
theorem weightF_app (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (k : Nat) (F : Value (tier (k + 2))) (G : Value (tier (k + 1))) (σ ε : Ordinal.{0})
    (hF : WeightF fix pow w (k + 1) σ F) (hG : WeightF fix pow w k ε G) (hS : ExpSep ε σ) :
    WeightF fix pow w k (ε + omegaIndex ^ σ) (F G) := by
  refine ⟨goodF_app h1 h2 k F G hF.1 hG.1, fun xs ss hxs hc => ?_⟩
  have h := hF.2 (Function.update xs (k + 1) G) (Function.update ss (k + 1) ε)
    (wEnv_update k xs ss G ε hxs hG) (condDown_update k ss ε σ hS hc)
  rw [expDown_update, appDown_update] at h
  exact h

end

theorem orbitWeight : OrbitWeight := by
  intro Z s add mul w one pow fix h1 h2 k Ψ Φ σ σ' hΨ hΦ hsep hb
  have eqs := orbitEquations (tier (k + 1)) Ψ Φ
  have og := orbitGood Z s add mul w one pow fix h1 h2 k Ψ Φ hΨ.1 hΦ.1
  have hpowpos : 0 < omegaIndex ^ σ := Ordinal.opow_pos σ omegaIndex_pos
  have nExp : ∀ a : CountableOrdinal, a.val ≠ 0 →
      coefficientNorm (σ' + omegaIndex ^ σ * a.val) =
        max (coefficientNorm σ') (max a.val (coefficientNorm σ)) :=
    fun a ha0 => nsepG_norm_mul hsep hb ha0 (countable_val_lt a)
  refine countable_induction _ ?_ ?_ ?_
  · intro a h0
    rw [eqs.1 a h0, h0, mul_zero, add_zero]
    exact hΦ
  · intro a' a ha ih
    have ha1 : 1 ≤ a.val := by rw [ha]; exact le_add_self
    have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    have ha'a : a'.val ≤ a.val := by rw [ha]; exact le_self_add
    have e1 : σ' + omegaIndex ^ σ * a'.val + omegaIndex ^ σ = σ' + omegaIndex ^ σ * a.val := by
      rw [ha, mul_add_one, add_assoc]
    have hS : ExpSep (σ' + omegaIndex ^ σ * a'.val) σ := by
      refine ⟨nsepG_step hsep hb (countable_val_lt a'), ?_, ?_⟩
      · rw [e1, nExp a ha0]
        by_cases ha'0 : a'.val = 0
        · rw [ha'0, mul_zero, add_zero]
          exact le_max_left _ _
        · rw [nExp a' ha'0]
          exact max_le_max le_rfl (max_le_max ha'a le_rfl)
      · rw [e1, nExp a ha0]
        exact (le_max_right _ _).trans (le_max_right _ _)
    have st := weightF_app h1 h2 k Ψ (orbit (tier (k + 1)) Ψ Φ a') σ
      (σ' + omegaIndex ^ σ * a'.val) hΨ ih hS
    rw [e1] at st
    rw [eqs.2.1 a' a ha]
    exact st
  · intro l hl ih
    refine ⟨og l, fun xs ss hxs hc => ?_⟩
    have gxs := wEnv_good k xs ss hxs
    have fam := orbit_family h1 h2 k Ψ Φ hΨ.1 hΦ.1 xs gxs
    have gl : GoodFn fix pow w (appDown k (orbit (tier (k + 1)) Ψ Φ l) xs) := (og l xs gxs).1
    obtain ⟨f1, f2, f3, f4⟩ := familyLifting.2 k ss l
      (fun β : CountableOrdinal => σ' + omegaIndex ^ σ * β.val) (σ' + omegaIndex ^ σ * l.val)
      hl.bot_lt (limFam_base hsep hb l hl) hc
    have hcβ : ∀ β : CountableOrdinal, β.val < l.val →
        CondDown k ss (σ' + omegaIndex ^ σ * β.val) := fun β hβ =>
      condDown_mono k ss (σ' + omegaIndex ^ σ * l.val) (σ' + omegaIndex ^ σ * β.val)
        ((add_le_add_iff_left σ').2 (mul_lt_mul_of_pos_left hβ hpowpos).le) hc
    exact stepLimit Z s add mul w one pow fix h1 h2 l
      (fun β => omegaIndex ^ expDown k ss (σ' + omegaIndex ^ σ * β.val))
      (omegaIndex ^ expDown k ss (σ' + omegaIndex ^ σ * l.val))
      (fun β => appDown k (orbit (tier (k + 1)) Ψ Φ β) xs)
      (appDown k (orbit (tier (k + 1)) Ψ Φ l) xs)
      (fun β hβ => ((ih β hβ).2 xs ss hxs (hcβ β hβ)).1)
      (fun β hβ => ((ih β hβ).2 xs ss hxs (hcβ β hβ)).2)
      f1 f2 f3 f4
      (fun β x hβ => fam_lt h1 h2 (fun a => appDown k (orbit (tier (k + 1)) Ψ Φ a) xs) fam β l hβ x)
      (fun x b Hb => fam_limit_le (fun a => appDown k (orbit (tier (k + 1)) Ψ Φ a) xs) fam l hl x b Hb)
      (fun x => gl.1.2 x) gl.2.2

theorem towerWeight : TowerWeight := by
  intro Z s add mul w one pow fix h1 h2 m
  have tg := towerGood Z s add mul w one pow fix h1 h2
  cases m with
  | zero =>
    refine ⟨tg 0, fun xs ss hxs hc => ?_⟩
    have hxs' : WEnv fix pow w 0 xs ss ∧
        WeightAt fix pow w 0 (WEnv fix pow w 0) (ss 1) (xs 1) := hxs
    have hc' : ExpSep (ss 1) 0 ∧
        omegaIndex ^ (ss 1 + omegaIndex ^ (0 : Ordinal.{0})) < endpoint := hc
    obtain ⟨⟨-, hnε, -⟩, hb⟩ := hc'
    rw [Ordinal.opow_zero] at hnε hb
    have gH : GoodFn fix pow w (xs 1) := (hxs'.2.1 xs trivial).1
    have hbε : omegaIndex ^ ss 1 < endpoint :=
      lt_trans ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (Order.lt_add_one_iff.2 le_rfl)) hb
    have stH : StepUp fix pow w (omegaIndex ^ ss 1) (xs 1) ∧
        StepLow fix pow w (omegaIndex ^ ss 1) (xs 1) := hxs'.2.2 xs ss trivial hbε
    have e1 : omegaIndex ^ ss 1 * omegaIndex = omegaIndex ^ (ss 1 + 1) :=
      (Ordinal.opow_add_one omegaIndex (ss 1)).symm
    have hnΩ : coefficientNorm (omegaIndex ^ ss 1) ≤
        coefficientNorm (omegaIndex ^ ss 1 * omegaIndex) := by
      rw [e1, norm_opow (ss 1) hbε, norm_opow (ss 1 + 1) hb]
      exact max_le_max le_rfl hnε
    have st := stepSuccessor Z s add mul w one pow fix h1 h2 (omegaIndex ^ ss 1) (xs 1)
      (normPrincipal_opow (ss 1) hb.le) hnΩ gH.1 gH.2.1 gH.2.2 stH.1 stH.2
    rw [e1] at st
    show StepUp fix pow w (omegaIndex ^ (ss 1 + omegaIndex ^ (0 : Ordinal.{0})))
        (towerValue fix 0 (xs 1)) ∧
      StepLow fix pow w (omegaIndex ^ (ss 1 + omegaIndex ^ (0 : Ordinal.{0})))
        (towerValue fix 0 (xs 1))
    rw [Ordinal.opow_zero]
    exact st
  | succ n =>
    refine ⟨tg (n + 1), fun xs ss hxs hc => ?_⟩
    have hxs' : (WEnv fix pow w n xs ss ∧
        WeightAt fix pow w n (WEnv fix pow w n) (ss (n + 1)) (xs (n + 1))) ∧
        WeightAt fix pow w (n + 1) (WEnv fix pow w (n + 1)) (ss (n + 2)) (xs (n + 2)) := hxs
    obtain ⟨⟨hn, hΦ⟩, hΨ⟩ := hxs'
    have hc' : ExpSep (ss (n + 2)) 0 ∧
        ExpSep (ss (n + 1)) (ss (n + 2) + omegaIndex ^ (0 : Ordinal.{0})) ∧
        CondDown n ss (ss (n + 1) +
          omegaIndex ^ (ss (n + 2) + omegaIndex ^ (0 : Ordinal.{0}))) := hc
    obtain ⟨⟨-, hσ1, -⟩, hS, hcn⟩ := hc'
    rw [Ordinal.opow_zero] at hσ1 hS hcn
    have hΛT : ss (n + 1) + omegaIndex ^ (ss (n + 2) + 1) < endpoint :=
      condDown_lt n ss (ss (n + 1) + omegaIndex ^ (ss (n + 2) + 1)) hcn
    have hb : omegaIndex ^ (ss (n + 2) + 1) ≤ endpoint := le_add_self.trans hΛT.le
    have hpowpos : 0 < omegaIndex ^ ss (n + 2) := Ordinal.opow_pos (ss (n + 2)) omegaIndex_pos
    have mulLt : ∀ a : CountableOrdinal,
        omegaIndex ^ ss (n + 2) * a.val < omegaIndex ^ (ss (n + 2) + 1) := by
      intro a
      rw [Ordinal.opow_add_one]
      exact mul_lt_mul_of_pos_left (countable_val_lt a) hpowpos
    have ow := orbitWeight Z s add mul w one pow fix h1 h2 n (xs (n + 2)) (xs (n + 1))
      (ss (n + 2)) (ss (n + 1)) hΨ hΦ hS.1 hb
    have gxs := wEnv_good n xs ss hn
    have fam := orbit_family h1 h2 n (xs (n + 2)) (xs (n + 1)) hΨ.1 hΦ.1 xs gxs
    obtain ⟨f1, f2, f3, f4⟩ := familyLifting.1 n ss
      (fun a : CountableOrdinal => ss (n + 1) + omegaIndex ^ ss (n + 2) * a.val)
      (ss (n + 1) + omegaIndex ^ (ss (n + 2) + 1)) (diagFam_base hS hσ1 hΛT) hcn
    have hca : ∀ a : CountableOrdinal,
        CondDown n ss (ss (n + 1) + omegaIndex ^ ss (n + 2) * a.val) := fun a =>
      condDown_mono n ss (ss (n + 1) + omegaIndex ^ (ss (n + 2) + 1))
        (ss (n + 1) + omegaIndex ^ ss (n + 2) * a.val)
        ((add_le_add_iff_left (ss (n + 1))).2 (mulLt a).le) hcn
    have st := stepDiagonal Z s add mul w one pow fix h1 h2
      (fun a => omegaIndex ^ expDown n ss (ss (n + 1) + omegaIndex ^ ss (n + 2) * a.val))
      (omegaIndex ^ expDown n ss (ss (n + 1) + omegaIndex ^ (ss (n + 2) + 1)))
      (fun a => appDown n (orbit (tier (n + 1)) (xs (n + 2)) (xs (n + 1)) a) xs)
      (fix (fun a => appDown n (orbit (tier (n + 1)) (xs (n + 2)) (xs (n + 1)) a) xs zeroValue))
      (fun a _ => ((ow a).2 xs ss hn (hca a)).1) (fun a _ => ((ow a).2 xs ss hn (hca a)).2)
      f1 f2 f3 f4
      (fun a b x h => fam_mono h1 h2 _ fam b a h x)
      (fun a x y h => (fam.1 a).1.1 x y h)
      (fun a => fam_diag_id_le h1 h2 _ fam a)
      (fun l hl b Hb => fam_limit_le _ fam l hl zeroValue b Hb)
      (fun κ hκ hpos => ⟨fam_fix_limit h1 h2 _ fam κ hκ hpos,
        fun a x ha hx => fam_fix_closed h1 h2 _ fam κ hκ hpos a x ha hx⟩)
      (fun κ hκ hΓ => fam_fix_crit h1 h2 _ fam κ hκ hΓ)
      (fun x => fam_spec h1 h2 _ fam x)
    show StepUp fix pow w
        (omegaIndex ^ expDown n ss (ss (n + 1) +
          omegaIndex ^ (ss (n + 2) + omegaIndex ^ (0 : Ordinal.{0}))))
        (appDown (n + 2) (towerValue fix (n + 1)) xs) ∧
      StepLow fix pow w
        (omegaIndex ^ expDown n ss (ss (n + 1) +
          omegaIndex ^ (ss (n + 2) + omegaIndex ^ (0 : Ordinal.{0}))))
        (appDown (n + 2) (towerValue fix (n + 1)) xs)
    rw [Ordinal.opow_zero, appDown_tower_succ fix n xs]
    exact st

#print axioms orbitWeight
#print axioms towerWeight

end LogicLineages.PersistentMarking.ActualCalibrationUniform
