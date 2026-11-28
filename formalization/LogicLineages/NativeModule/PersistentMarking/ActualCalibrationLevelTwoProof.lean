module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelTwoWeightProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePowerProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsProof

@[expose] public section

/-! Level 2 of the calibration: the collapse along `Ω^(Ω^e)` is the level-2 diagonal
`e ↦ (B_1^e B_0) N_B 0` below its first fixed point (`PsiTowerLevelAt 2`), the function-side
facts (`LevelFactsAt 2`), and hence `Δ_4' = ψ(a_4)` through `exact_CalibrationStep`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationLevels ActualTowerIndex Paper16RemainingOrdinalTargets
open scoped Ordinal

/-- A strictly increasing function on the countable ordinals is weakly inflationary. -/
theorem strict_id_le (f : CountableOrdinal → CountableOrdinal)
    (hs : ∀ a b : CountableOrdinal, a.val < b.val → (f a).val < (f b).val) :
    ∀ a : CountableOrdinal, a.val ≤ (f a).val := by
  refine countable_strong_induction _ (fun a ih => ?_)
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (ih (f a) hlt) (not_le.2 (hs (f a) a hlt))

/-- If `Θ > 1` is closed under a strictly increasing, limit-continuous `f` on `[1, Θ)`, then `f`
has a fixed point in `[1, Θ]`. -/
theorem diag_closed_fix (f : CountableOrdinal → CountableOrdinal)
    (hs : ∀ a b : CountableOrdinal, a.val < b.val → (f a).val < (f b).val)
    (hlim : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ b : Ordinal.{0},
      (∀ a : CountableOrdinal, a.val < l.val → (f a).val ≤ b) → (f l).val ≤ b)
    (Θ : CountableOrdinal) (hΘ : 1 < Θ.val)
    (H : ∀ e : CountableOrdinal, 1 ≤ e.val → e.val < Θ.val → (f e).val < Θ.val) :
    ∃ θ : CountableOrdinal, 1 ≤ θ.val ∧ θ.val ≤ Θ.val ∧ f θ = θ := by
  rcases countable_cases Θ with h0 | ⟨c, hc⟩ | hl
  · exact absurd hΘ (by rw [h0]; exact not_lt.2 zero_le_one)
  · have hcΘ : c.val < Θ.val := by rw [hc]; exact Order.lt_add_one_iff.2 le_rfl
    have c1 : 1 ≤ c.val := by
      have h := hΘ
      rw [hc] at h
      exact Order.lt_add_one_iff.1 h
    have a := H c c1 hcΘ
    rw [hc] at a
    exact ⟨c, c1, hcΘ.le,
      Subtype.ext (le_antisymm (Order.lt_add_one_iff.1 a) (strict_id_le f hs c))⟩
  · refine ⟨Θ, hΘ.le, le_rfl, Subtype.ext (le_antisymm ?_ (strict_id_le f hs Θ))⟩
    refine hlim Θ hl Θ.val (fun β hβ => ?_)
    obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
    have o1Θ : o1.val < Θ.val := by rw [ho1]; exact hΘ
    have o11 : 1 ≤ o1.val := le_of_eq ho1.symm
    rcases lt_or_ge β.val o1.val with h | h
    · exact (lt_trans (hs β o1 h) (H o1 o11 o1Θ)).le
    · exact (H β (o11.trans h) hβ).le

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem goodVeblen (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    GoodFn fix pow w (veblenValue fix pow) :=
  ⟨veblen_monoInfl h1 h2, fun _ => le_rfl, fun x hx => crit_succ x hx⟩

/-- `Γ_0 < B_0 N_B 0`. -/
theorem base_lt_b0 (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    (baseValue fix pow w).val < (towerValue fix 0 (veblenValue fix pow) zeroValue).val := by
  have gN : GoodFn fix pow w (veblenValue fix pow) := goodVeblen h1 h2
  obtain ⟨hfix, hpos, -⟩ := b0_spec h1 h2 (veblenValue fix pow) gN.1 zeroValue
  have big := gfix_gt_omega h1 h2 (veblenValue fix pow) gN.1 gN.2.1
    (towerValue fix 0 (veblenValue fix pow) zeroValue) hfix hpos
  exact gfix_closed h1 h2 (veblenValue fix pow) gN.1 gN.2.1
    (towerValue fix 0 (veblenValue fix pow) zeroValue) hfix hpos w (by rw [h2.1]; exact big)

/-- For `e ≥ 1`, the level-2 function restarts below its value at 0. -/
theorem levelTwo_restart (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ e : CountableOrdinal, 1 ≤ e.val → ∀ y : CountableOrdinal,
      y.val < (levelTwo fix e (veblenValue fix pow) zeroValue).val →
      (levelTwo fix e (veblenValue fix pow) y).val ≤
        (levelTwo fix e (veblenValue fix pow) zeroValue).val := by
  have eqs := orbitEquations (tier 2) (towerValue fix 1) (towerValue fix 0)
  obtain ⟨ltGood, ltMono, -⟩ := levelTwoGood Z s add mul w one pow fix h1 h2
  have gN : GoodFn fix pow w (veblenValue fix pow) := goodVeblen h1 h2
  refine countable_induction _ ?_ ?_ ?_
  · intro e h0 h1e
    rw [h0] at h1e
    exact absurd h1e (not_le.2 zero_lt_one)
  · intro e' e he _ _ y hy
    have eeq : levelTwo fix e = towerValue fix 1 (levelTwo fix e') := eqs.2.1 e' e he
    rw [eeq] at hy ⊢
    obtain ⟨hfix, -, -⟩ :=
      b1_spec h1 h2 (levelTwo fix e') (ltGood e') (veblenValue fix pow) gN zeroValue
    exact (b1_spec h1 h2 (levelTwo fix e') (ltGood e') (veblenValue fix pow) gN y).2.2
      (towerValue fix 1 (levelTwo fix e') (veblenValue fix pow) zeroValue) hy hfix
  · intro l hl ih _ y hy
    have sup : ∀ x : CountableOrdinal, (levelTwo fix l (veblenValue fix pow) x).val =
        ⨆ i : EarlierStages l, (levelTwo fix (earlierStage l i) (veblenValue fix pow) x).val :=
      fun x => eqs.2.2 l hl (veblenValue fix pow) x
    haveI : Nonempty (EarlierStages l) := ⟨⟨0, hl.bot_lt⟩⟩
    have hy' := hy
    rw [sup zeroValue] at hy'
    obtain ⟨i, hi⟩ := (lt_ciSup_iff (bddAbove_orbit .base id (fun i : EarlierStages l =>
      levelTwo fix (earlierStage l i) (veblenValue fix pow) zeroValue))).1 hy'
    rw [sup y]
    refine ciSup_le' (fun j => ?_)
    have hmax : max (max j.val i.val) 1 < l.val :=
      max_lt (max_lt j.property i.property) (Ordinal.one_lt_of_isSuccLimit hl)
    obtain ⟨m, hm⟩ := countable_mk (max (max j.val i.val) 1) (hmax.trans (countable_val_lt l))
    have hml : m.val < l.val := by rw [hm]; exact hmax
    have hjm : (earlierStage l j).val ≤ m.val := by
      rw [hm]
      exact (le_max_left j.val i.val).trans (le_max_left _ _)
    have him : (earlierStage l i).val ≤ m.val := by
      rw [hm]
      exact (le_max_right j.val i.val).trans (le_max_left _ _)
    have a := ltMono (earlierStage l j) m (veblenValue fix pow) gN hjm y
    have hyim : y.val < (levelTwo fix m (veblenValue fix pow) zeroValue).val :=
      lt_of_lt_of_le hi (ltMono (earlierStage l i) m (veblenValue fix pow) gN him zeroValue)
    have b := ih m hml (by rw [hm]; exact le_max_right _ _) y hyim
    exact (a.trans b).trans (ltMono m l (veblenValue fix pow) gN hml.le zeroValue)

/-- The collapse along `Ω^(Ω^e)`, in `psiO` form. -/
theorem psiO_tower_two (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ e : CountableOrdinal, 1 ≤ e.val →
      (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val →
        levelTwo fix θ (veblenValue fix pow) zeroValue ≠ θ) →
      psiO fix pow w (omegaIndex ^ (omegaIndex ^ e.val)) =
        (levelTwo fix e (veblenValue fix pow) zeroValue).val := by
  obtain ⟨ltGood, ltMono, ltStrict⟩ := levelTwoGood Z s add mul w one pow fix h1 h2
  have gN : GoodFn fix pow w (veblenValue fix pow) := goodVeblen h1 h2
  have eqs := orbitEquations (tier 2) (towerValue fix 1) (towerValue fix 0)
  have a4 : argument 4 = omegaIndex ^ (omegaIndex ^ omegaIndex) :=
    (argument_succ 3).trans (congrArg (omegaIndex ^ ·) argument_three)
  have hbnd : ∀ e : CountableOrdinal, omegaIndex ^ (omegaIndex ^ e.val) < endpoint := fun e =>
    lt_trans ((Ordinal.opow_lt_opow_iff_right one_lt_index).2
        ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (countable_val_lt e)))
      (lt_of_eq_of_lt a4.symm (exact_BelowEndpoint 4))
  have strictD : ∀ a b : CountableOrdinal, a.val < b.val →
      (levelTwo fix a (veblenValue fix pow) zeroValue).val <
        (levelTwo fix b (veblenValue fix pow) zeroValue).val := by
    intro a b hab
    obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1)
      ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
    have ha1b : a1.val ≤ b.val := by rw [ha1]; exact Order.add_one_le_of_lt hab
    exact lt_of_lt_of_le (ltStrict a a1 (veblenValue fix pow) gN ha1 zeroValue)
      (ltMono a1 b (veblenValue fix pow) gN ha1b zeroValue)
  have limD : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ b : Ordinal.{0},
      (∀ a : CountableOrdinal, a.val < l.val →
        (levelTwo fix a (veblenValue fix pow) zeroValue).val ≤ b) →
      (levelTwo fix l (veblenValue fix pow) zeroValue).val ≤ b := by
    intro l hl b Hb
    have sup : (levelTwo fix l (veblenValue fix pow) zeroValue).val =
        ⨆ i : EarlierStages l,
          (levelTwo fix (earlierStage l i) (veblenValue fix pow) zeroValue).val :=
      eqs.2.2 l hl (veblenValue fix pow) zeroValue
    rw [sup]
    exact ciSup_le' (fun i => Hb (earlierStage l i) i.property)
  have sb := stepBase Z s add mul w one pow fix h1 h2
  have step0 : IsStep fix pow w 0 (veblenValue fix pow) := by
    refine ⟨gN, ?_, ?_⟩
    · rw [Ordinal.opow_zero]
      exact sb.1
    · rw [Ordinal.opow_zero]
      exact sb.2
  refine countable_strong_induction _ (fun e ih he1 hnofix => ?_)
  have hb := hbnd e
  have hend : omegaIndex ^ (omegaIndex ^ e.val) ≤ endpoint := hb.le
  have hnp : coefficientNorm (omegaIndex ^ e.val) = e.val := norm_power e he1
  have hc : ExpCond 0 e.val := by
    refine ⟨nsep_zero e.val, ?_, ?_, ?_⟩
    · rw [cnorm_zero]
      exact ozl _
    · exact le_of_eq (by rw [zero_add, hnp])
    · rw [zero_add]
      exact hb
  have stp := levelTwoWeight Z s add mul w one pow fix h1 h2 e 0 (veblenValue fix pow) hc step0
  rw [zero_add] at stp
  have ctx : StepContext 0 (omegaIndex ^ (omegaIndex ^ e.val)) := by
    refine ⟨?_, fun τ _ => ?_⟩
    · rw [zero_add]
      exact hend
    · rw [zero_add, cnorm_zero]
      exact (max_eq_right (ozl _)).symm
  have up := stp.2.1 0 (baseValue fix pow w) ctx crit_base (psiO_zero_le h1 h2)
  rw [zero_add] at up
  have hΓ : (baseValue fix pow w).val < (levelTwo fix e (veblenValue fix pow) zeroValue).val :=
    lt_of_lt_of_le (base_lt_b0 h1 h2) ((ltGood e (veblenValue fix pow) gN).2 zeroValue)
  have up' : psiO fix pow w (omegaIndex ^ (omegaIndex ^ e.val)) ≤
      (levelTwo fix e (veblenValue fix pow) zeroValue).val :=
    up.trans (levelTwo_restart h1 h2 e he1 (baseValue fix pow w) hΓ)
  have nTop : coefficientNorm (omegaIndex ^ (omegaIndex ^ e.val)) = e.val := by
    rw [norm_opow (omegaIndex ^ e.val) hb, hnp]
    exact max_eq_right he1
  have act : e.val < psiO fix pow w (omegaIndex ^ (omegaIndex ^ e.val)) := by
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
        (levelTwo fix e' (veblenValue fix pow) zeroValue).val < Θ.val := by
      intro e' he'1 he'Θ
      have he'e : e'.val < e.val := lt_of_lt_of_le he'Θ hΘe
      have hpow : omegaIndex ^ (omegaIndex ^ e'.val) < omegaIndex ^ (omegaIndex ^ e.val) :=
        (Ordinal.opow_lt_opow_iff_right one_lt_index).2
          ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 he'e)
      have hn' : coefficientNorm (omegaIndex ^ (omegaIndex ^ e'.val)) = e'.val := by
        rw [norm_opow (omegaIndex ^ e'.val) (hbnd e'), norm_power e' he'1]
        exact max_eq_right he'1
      have cl := psiO_closure (w := w) h1 h2 hend hpow (by rw [hn', ← hΘ]; exact he'Θ)
      rw [ih e' he'e he'1 (fun θ' a b => hnofix θ' a (b.trans he'e.le)), ← hΘ] at cl
      exact cl
    obtain ⟨θ, hθ1, hθΘ, hfix⟩ := diag_closed_fix
      (fun a => levelTwo fix a (veblenValue fix pow) zeroValue) strictD limD Θ hΘ1 H
    exact hnofix θ hθ1 (hθΘ.trans hΘe) hfix
  have low := stp.2.2 0 zeroValue ctx
    (by rw [cnorm_zero, zero_add]; exact lt_of_le_of_lt (ozl _) act)
    (by rw [zero_add, nTop]; exact act) (ozl _)
  rw [zero_add] at low
  exact le_antisymm up' low

end

theorem levelFactsAt_two (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : LevelFactsAt fix pow w 2 := by
  obtain ⟨ltGood, ltMono, ltStrict⟩ := levelTwoGood Z s add mul w one pow fix h1 h2
  have gN : GoodFn fix pow w (veblenValue fix pow) := goodVeblen h1 h2
  refine ⟨fun α β hαβ => ?_, fun e _ => ?_, fun lim hl => ?_⟩
  · obtain ⟨α1, hα1⟩ := countable_mk (α.val + 1)
      ((isSuccLimit_omega 1).add_one_lt (countable_val_lt α))
    have hα1β : α1.val ≤ β.val := by rw [hα1]; exact Order.add_one_le_of_lt hαβ
    exact lt_of_lt_of_le (ltStrict α α1 (veblenValue fix pow) gN hα1 zeroValue)
      (ltMono α1 β (veblenValue fix pow) gN hα1β zeroValue)
  · exact lt_of_lt_of_le (base_lt_b0 h1 h2) ((ltGood e (veblenValue fix pow) gN).2 zeroValue)
  · exact (orbitEquations (tier 2) (towerValue fix 1) (towerValue fix 0)).2.2 lim hl
      (veblenValue fix pow) zeroValue

theorem psiTowerLevelAt_two (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : PsiTowerLevelAt fix pow w 2 := by
  intro e he1 hnofix h
  have h' : omegaIndex ^ (omegaIndex ^ e.val) ≤ endpoint := h
  have r := psiO_tower_two (w := w) h1 h2 e he1 hnofix
  rw [psiO_eq h'] at r
  exact r

/-- `Δ_4' = ψ(a_4)` for the actual collapse of every solution. -/
theorem calibrationAt_four (A : OrdinalSemantics) : CalibrationAt A 4 :=
  ActualCalibrationLevelsProof.exact_CalibrationStep A.zero A.successor A.add A.mul A.omega A.one
    A.pow A.fix A.arithmetic A.omegaEquations 2
    (levelFactsAt_two A.zero A.successor A.add A.mul A.omega A.one A.pow A.fix A.arithmetic
      A.omegaEquations)
    (psiTowerLevelAt_two A.zero A.successor A.add A.mul A.omega A.one A.pow A.fix A.arithmetic
      A.omegaEquations)

#print axioms levelFactsAt_two
#print axioms psiTowerLevelAt_two
#print axioms calibrationAt_four

end LogicLineages.PersistentMarking.ActualCalibrationStep
