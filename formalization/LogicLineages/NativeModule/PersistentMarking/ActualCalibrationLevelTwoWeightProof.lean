module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelTwoFunctionProof

@[expose] public section

/-! Weights at type `A_2`: if a good operator `G` adds `Ω^e` to the exponent of every step, then
`B_1 G` adds `Ω^(e+1)` (the diagonal lemma on the family `(Ω^(ε + Ω^e·a), G^a H)`, whose members
are steps by induction on `a`, with the limit rule at limits); hence `B_1^e B_0` adds `Ω^e`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-- An index in `[Ω^(ε+δ), Ω^(ε+T))` has leading exponent `ε + ρ` with `δ ≤ ρ < T`, and its norm
dominates `1`, `|ε|` and `|ρ|`, when the norm of `ε` separates below `T`. -/
theorem log_split {ε T δ τ : Ordinal.{0}}
    (hsep : ∀ ρ : Ordinal.{0}, ρ < T →
      coefficientNorm (ε + ρ) = max (coefficientNorm ε) (coefficientNorm ρ))
    (hle : omegaIndex ^ (ε + δ) ≤ τ) (hτ : τ < omegaIndex ^ (ε + T))
    (hΛ : omegaIndex ^ (ε + T) < endpoint) :
    ∃ ρ : Ordinal.{0}, δ ≤ ρ ∧ ρ < T ∧
      max 1 (max (coefficientNorm ε) (coefficientNorm ρ)) ≤ coefficientNorm τ := by
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact absurd hle (not_le.2 (Ordinal.opow_pos (ε + δ) omegaIndex_pos))
  have hτΛ : τ < endpoint := lt_trans hτ hΛ
  have hlog1 : ε + δ ≤ Ordinal.log omegaIndex τ := Ordinal.le_log_of_opow_le one_lt_index hle
  have hlog2 : Ordinal.log omegaIndex τ < ε + T :=
    (Ordinal.lt_opow_iff_log_lt one_lt_index hτ0).1 hτ
  have hεlog : ε ≤ Ordinal.log omegaIndex τ := le_self_add.trans hlog1
  have hρT : Ordinal.log omegaIndex τ - ε < T := (Ordinal.sub_lt_of_le hεlog).2 hlog2
  refine ⟨Ordinal.log omegaIndex τ - ε, (Ordinal.le_sub_of_le hεlog).2 hlog1, hρT, ?_⟩
  have hnl := hsep (Ordinal.log omegaIndex τ - ε) hρT
  rw [Ordinal.add_sub_cancel_of_le hεlog] at hnl
  rw [← hnl]
  exact norm_ge_log τ hτ0 hτΛ

theorem opWeightSuccessor : OpWeightSuccessor := by
  intro Z s add mul w one pow fix h1 h2 G e e' he hG hW ε H hcond hstep
  obtain ⟨hsep, hnε, hne, hb⟩ := hcond
  rw [he] at hsep hnε hne hb ⊢
  have hE : e.val < omegaIndex := countable_val_lt e
  have hpowpos : 0 < omegaIndex ^ e.val := Ordinal.opow_pos e.val omegaIndex_pos
  have eqs := orbitEquations (tier 1) G H
  have good := op_orbit_good h1 h2 G hG H hstep.1
  have mulLt : ∀ a : CountableOrdinal,
      omegaIndex ^ e.val * a.val < omegaIndex ^ (e.val + 1) := by
    intro a
    rw [Ordinal.opow_add_one]
    exact mul_lt_mul_of_pos_left (countable_val_lt a) hpowpos
  have powLt : ∀ a : CountableOrdinal, omegaIndex ^ (ε + omegaIndex ^ e.val * a.val) <
      omegaIndex ^ (ε + omegaIndex ^ (e.val + 1)) :=
    fun a => (Ordinal.opow_lt_opow_iff_right one_lt_index).2 ((add_lt_add_iff_left ε).2 (mulLt a))
  have bLt : ∀ a : CountableOrdinal, omegaIndex ^ (ε + omegaIndex ^ e.val * a.val) < endpoint :=
    fun a => lt_trans (powLt a) hb
  have nExp : ∀ a : CountableOrdinal, a.val ≠ 0 →
      coefficientNorm (ε + omegaIndex ^ e.val * a.val) =
        max (coefficientNorm ε) (max a.val e.val) :=
    fun a ha0 => nsep_norm_mul hsep hE ha0 (countable_val_lt a)
  have nExpLe : ∀ a : CountableOrdinal,
      coefficientNorm (ε + omegaIndex ^ e.val * a.val) ≤
        max (coefficientNorm ε) (max a.val e.val) := by
    intro a
    by_cases ha0 : a.val = 0
    · rw [ha0, mul_zero, add_zero]
      exact le_max_left _ _
    · exact le_of_eq (nExp a ha0)
  have nPow : ∀ a : CountableOrdinal,
      coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ e.val * a.val)) =
        max 1 (coefficientNorm (ε + omegaIndex ^ e.val * a.val)) :=
    fun a => norm_opow (ε + omegaIndex ^ e.val * a.val) (bLt a)
  have nTop : coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ (e.val + 1))) =
      max 1 (coefficientNorm (ε + omegaIndex ^ (e.val + 1))) :=
    norm_opow (ε + omegaIndex ^ (e.val + 1)) hb
  -- the members of the family are steps
  have chain : ∀ a : CountableOrdinal,
      IsStep fix pow w (ε + omegaIndex ^ e.val * a.val) (orbit (tier 1) G H a) := by
    refine countable_induction _ ?_ ?_ ?_
    · intro a h0
      rw [eqs.1 a h0, h0, mul_zero, add_zero]
      exact hstep
    · intro a' a ha ih
      have ha1 : 1 ≤ a.val := by rw [ha]; exact le_add_self
      have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
      have ha'a : a'.val ≤ a.val := by rw [ha]; exact le_self_add
      have e1 : ε + omegaIndex ^ e.val * a'.val + omegaIndex ^ e.val =
          ε + omegaIndex ^ e.val * a.val := by
        rw [ha, mul_add_one, add_assoc]
      have hc : ExpCond (ε + omegaIndex ^ e.val * a'.val) e.val := by
        refine ⟨nsep_step hsep hE (countable_val_lt a'), ?_, ?_, ?_⟩
        · rw [e1, nExp a ha0]
          exact (nExpLe a').trans (max_le_max le_rfl (max_le_max ha'a le_rfl))
        · rw [e1, nExp a ha0]
          exact (le_max_right _ _).trans (le_max_right _ _)
        · rw [e1]
          exact bLt a
      have st := hW (ε + omegaIndex ^ e.val * a'.val) (orbit (tier 1) G H a') hc ih
      rw [e1] at st
      rw [eqs.2.1 a' a ha]
      exact st
    · intro l hl ih
      have hlΩ : l.val < omegaIndex := countable_val_lt l
      have hl0 : l.val ≠ 0 := hl.ne_bot
      have gl := good l
      have sup : ∀ x : CountableOrdinal, (orbit (tier 1) G H l x).val =
          ⨆ i : EarlierStages l, (orbit (tier 1) G H (earlierStage l i) x).val :=
        fun x => eqs.2.2 l hl x
      have hsupl : ∀ (x : CountableOrdinal) (b : Ordinal.{0}),
          (∀ β : CountableOrdinal, β.val < l.val → (orbit (tier 1) G H β x).val ≤ b) →
          (orbit (tier 1) G H l x).val ≤ b := by
        intro x b Hb
        rw [sup x]
        exact ciSup_le' (fun i => Hb (earlierStage l i) i.property)
      have strict : ∀ β x : CountableOrdinal, β.val < l.val →
          (orbit (tier 1) G H β x).val < (orbit (tier 1) G H l x).val := by
        intro β x hβ
        obtain ⟨β1, hβ1⟩ := countable_mk (β.val + 1)
          ((isSuccLimit_omega 1).add_one_lt (countable_val_lt β))
        have hβ1l : β1.val ≤ l.val := by rw [hβ1]; exact (hl.add_one_lt hβ).le
        exact lt_of_lt_of_le (op_orbit_strict h1 h2 G hG H hstep.1 β β1 hβ1 x) (gl.2 β1 hβ1l x)
      have hmullim : Order.IsSuccLimit (omegaIndex ^ e.val * l.val) :=
        Ordinal.isSuccLimit_mul_right hpowpos hl
      have hcofl : ∀ τ : Ordinal.{0}, τ < omegaIndex ^ (ε + omegaIndex ^ e.val * l.val) →
          ∃ β : CountableOrdinal, β.val < l.val ∧
            τ < omegaIndex ^ (ε + omegaIndex ^ e.val * β.val) := by
        intro τ hτ
        obtain ⟨c', hc', hτc⟩ := (Ordinal.lt_opow_of_isSuccLimit omegaIndex_ne
          (Ordinal.isSuccLimit_add ε hmullim)).1 hτ
        obtain ⟨d, hd, hcd⟩ := (Ordinal.lt_add_iff hmullim.ne_bot).1 hc'
        obtain ⟨c'', hc''l, hdc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hl).1 hd
        obtain ⟨β, hβ⟩ := countable_mk c'' (hc''l.trans hlΩ)
        refine ⟨β, by rw [hβ]; exact hc''l, ?_⟩
        rw [hβ]
        exact lt_of_lt_of_le hτc (Ordinal.opow_le_opow_right omegaIndex_pos
          (hcd.trans ((add_le_add_iff_left ε).2 hdc.le)))
      have hn1l : ∀ β : CountableOrdinal, β.val < l.val →
          coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ e.val * β.val)) ≤
            coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ e.val * l.val)) := by
        intro β hβ
        rw [nPow β, nPow l, nExp l hl0]
        exact max_le_max le_rfl
          ((nExpLe β).trans (max_le_max le_rfl (max_le_max hβ.le le_rfl)))
      have hn2l : ∀ (β : CountableOrdinal) (τ : Ordinal.{0}), β.val < l.val →
          omegaIndex ^ (ε + omegaIndex ^ e.val * β.val) ≤ τ →
          τ < omegaIndex ^ (ε + omegaIndex ^ e.val * l.val) →
          coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ e.val * β.val)) ≤ coefficientNorm τ := by
        intro β τ _ hle hτ
        obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := log_split hsep hle (lt_trans hτ (powLt l)) hb
        rw [nPow β]
        refine le_trans (max_le_max le_rfl ?_) hρ3
        by_cases hβ0 : β.val = 0
        · rw [hβ0, mul_zero, add_zero]
          exact le_max_left _ _
        · rw [nExp β hβ0]
          exact max_le_max le_rfl (norm_ge_of_mul_le e.val β.val ρ hE
            (Order.one_le_iff_ne_zero.2 hβ0) hρ1 hρ2)
      have st := stepLimit Z s add mul w one pow fix h1 h2 l
        (fun β => omegaIndex ^ (ε + omegaIndex ^ e.val * β.val))
        (omegaIndex ^ (ε + omegaIndex ^ e.val * l.val))
        (fun β => orbit (tier 1) G H β) (orbit (tier 1) G H l)
        (fun β hβ => (ih β hβ).2.1) (fun β hβ => (ih β hβ).2.2)
        (fun β hβ => (Ordinal.opow_lt_opow_iff_right one_lt_index).2
          ((add_lt_add_iff_left ε).2 (mul_lt_mul_of_pos_left hβ hpowpos)))
        hcofl hn1l hn2l strict hsupl (fun x => gl.1.1.2 x) gl.1.2.2
      exact ⟨gl.1, st.1, st.2⟩
  -- the hypotheses of the diagonal lemma
  have hcof : ∀ τ : Ordinal.{0}, τ < omegaIndex ^ (ε + omegaIndex ^ (e.val + 1)) →
      ∃ a b : CountableOrdinal, b.val = a.val + 1 ∧ a.val ≤ coefficientNorm τ ∧
        τ < omegaIndex ^ (ε + omegaIndex ^ e.val * b.val) := by
    intro τ hτ
    obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
    have ho1' : o1.val = zeroValue.val + 1 := ho1.trans (zero_add (1 : Ordinal.{0})).symm
    have base : omegaIndex ^ ε ≤ omegaIndex ^ (ε + omegaIndex ^ e.val * o1.val) :=
      Ordinal.opow_le_opow_right omegaIndex_pos le_self_add
    by_cases hτ0 : τ = 0
    · refine ⟨zeroValue, o1, ho1', ozl _, ?_⟩
      rw [hτ0]
      exact Ordinal.opow_pos _ omegaIndex_pos
    · have hτΛ : τ < endpoint := lt_trans hτ hb
      have hlog : Ordinal.log omegaIndex τ < ε + omegaIndex ^ (e.val + 1) :=
        (Ordinal.lt_opow_iff_log_lt one_lt_index hτ0).1 hτ
      have hτs : τ < omegaIndex ^ (Ordinal.log omegaIndex τ + 1) := by
        have h := Ordinal.lt_opow_succ_log_self one_lt_index τ
        rw [← Ordinal.add_one_eq_succ] at h
        exact h
      rcases lt_or_ge (Ordinal.log omegaIndex τ) ε with hlt | hge
      · refine ⟨zeroValue, o1, ho1', ozl _, ?_⟩
        exact lt_of_lt_of_le hτs ((Ordinal.opow_le_opow_right omegaIndex_pos
          (Order.add_one_le_of_lt hlt)).trans base)
      · have hρ : Ordinal.log omegaIndex τ - ε < omegaIndex ^ (e.val + 1) :=
          (Ordinal.sub_lt_of_le hge).2 hlog
        obtain ⟨b0, hb0Ω, hb0n, hρb⟩ :=
          norm_div_le e.val (Ordinal.log omegaIndex τ - ε) hE hρ
        obtain ⟨a, ha⟩ := countable_mk b0 hb0Ω
        obtain ⟨b, hb'⟩ := countable_mk (a.val + 1)
          ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
        have hnl := hsep (Ordinal.log omegaIndex τ - ε) hρ
        rw [Ordinal.add_sub_cancel_of_le hge] at hnl
        have hnτ := norm_ge_log τ hτ0 hτΛ
        refine ⟨a, b, hb', ?_, ?_⟩
        · rw [ha]
          exact hb0n.trans (((le_max_right _ _).trans (le_of_eq hnl.symm)).trans
            ((le_max_right _ _).trans hnτ))
        · have hL : Ordinal.log omegaIndex τ < ε + omegaIndex ^ e.val * b.val := by
            rw [hb', ha]
            exact lt_of_eq_of_lt (Ordinal.add_sub_cancel_of_le hge).symm
              ((add_lt_add_iff_left ε).2 hρb)
          exact lt_of_lt_of_le hτs
            (Ordinal.opow_le_opow_right omegaIndex_pos (Order.add_one_le_of_lt hL))
  have hn1 : ∀ a : CountableOrdinal, 1 ≤ a.val →
      coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ e.val * a.val)) ≤
        max (coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ (e.val + 1)))) a.val := by
    intro a ha1
    have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    rw [nPow a, nExp a ha0, nTop]
    refine max_le ((le_max_left _ _).trans (le_max_left _ _))
      (max_le ?_ (max_le (le_max_right _ _) ?_))
    · exact (hnε.trans (le_max_right _ _)).trans (le_max_left _ _)
    · exact ((le_self_add.trans hne).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hn2 : ∀ (a : CountableOrdinal) (τ : Ordinal.{0}), 1 ≤ a.val →
      omegaIndex ^ (ε + omegaIndex ^ e.val * a.val) ≤ τ →
      τ < omegaIndex ^ (ε + omegaIndex ^ (e.val + 1)) →
      coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ e.val * a.val)) ≤ coefficientNorm τ := by
    intro a τ ha1 hle hτ
    have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := log_split hsep hle hτ hb
    rw [nPow a, nExp a ha0]
    exact le_trans (max_le_max le_rfl (max_le_max le_rfl
      (norm_ge_of_mul_le e.val a.val ρ hE ha1 hρ1 hρ2))) hρ3
  have st := stepDiagonal Z s add mul w one pow fix h1 h2
    (fun a => omegaIndex ^ (ε + omegaIndex ^ e.val * a.val))
    (omegaIndex ^ (ε + omegaIndex ^ (e.val + 1)))
    (fun a => orbit (tier 1) G H a) (towerValue fix 1 G H)
    (fun a _ => (chain a).2.1) (fun a _ => (chain a).2.2) powLt hcof hn1 hn2
    (fun a b x h => (good b).2 a h x) (fun a x y h => (good a).1.1.1 x y h)
    (fun a => op_diag_id_le h1 h2 G hG H hstep.1 a)
    (fun l hl b Hb => op_diag_limit_le G H l hl b Hb)
    (fun κ hκ hpos => ⟨op_fix_limit h1 h2 G hG H hstep.1 κ hκ hpos,
      fun a x ha hx => op_fix_closed h1 h2 G hG H hstep.1 κ hκ hpos a x ha hx⟩)
    (fun κ hκ hΓ => op_fix_crit h1 h2 G hG H hstep.1 κ hκ hΓ)
    (fun x => b1_spec h1 h2 G hG H hstep.1 x)
  exact ⟨((opSuccessor Z s add mul w one pow fix h1 h2 G hG).1 H hstep.1).1, st.1, st.2⟩

theorem levelTwoWeight : LevelTwoWeight := by
  intro Z s add mul w one pow fix h1 h2
  have eqs := orbitEquations (tier 2) (towerValue fix 1) (towerValue fix 0)
  obtain ⟨ltGood, ltMono, ltStrict⟩ := levelTwoGood Z s add mul w one pow fix h1 h2
  refine countable_induction _ ?_ ?_ ?_
  · intro e h0 ε H hcond hstep
    obtain ⟨-, hnε, -, hb⟩ := hcond
    rw [h0, Ordinal.opow_zero] at hnε hb ⊢
    have e0eq : levelTwo fix e = towerValue fix 0 := eqs.1 e h0
    rw [e0eq]
    have hbε : omegaIndex ^ ε < endpoint :=
      lt_trans ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (Order.lt_add_one_iff.2 le_rfl)) hb
    have e1 : omegaIndex ^ ε * omegaIndex = omegaIndex ^ (ε + 1) :=
      (Ordinal.opow_add_one omegaIndex ε).symm
    have hnΩ : coefficientNorm (omegaIndex ^ ε) ≤ coefficientNorm (omegaIndex ^ ε * omegaIndex) := by
      rw [e1, norm_opow ε hbε, norm_opow (ε + 1) hb]
      exact max_le_max le_rfl hnε
    have st := stepSuccessor Z s add mul w one pow fix h1 h2 (omegaIndex ^ ε) H
      (normPrincipal_opow ε hb.le) hnΩ hstep.1.1 hstep.1.2.1 hstep.1.2.2 hstep.2.1 hstep.2.2
    rw [e1] at st
    exact ⟨(good_b0 h1 h2 H hstep.1).1, st.1, st.2⟩
  · intro e' e he ih ε H hcond hstep
    have eeq : levelTwo fix e = towerValue fix 1 (levelTwo fix e') := eqs.2.1 e' e he
    rw [eeq]
    exact opWeightSuccessor Z s add mul w one pow fix h1 h2 (levelTwo fix e') e' e he (ltGood e')
      ih ε H hcond hstep
  · intro l hl ih ε H hcond hstep
    obtain ⟨hsep, hnε, hnl, hb⟩ := hcond
    have hlΩ : l.val < omegaIndex := countable_val_lt l
    have gl := (ltGood l H hstep.1).1
    have sup : ∀ x : CountableOrdinal, (levelTwo fix l H x).val =
        ⨆ i : EarlierStages l, (levelTwo fix (earlierStage l i) H x).val :=
      fun x => eqs.2.2 l hl H x
    have powβ : ∀ β : CountableOrdinal, β.val < l.val →
        omegaIndex ^ β.val < omegaIndex ^ l.val :=
      fun β hβ => (Ordinal.opow_lt_opow_iff_right one_lt_index).2 hβ
    have nExp : ∀ β : CountableOrdinal, β.val < l.val →
        coefficientNorm (ε + omegaIndex ^ β.val) = max (coefficientNorm ε) (max 1 β.val) := by
      intro β hβ
      have h := norm_pow β.val 1 (countable_val_lt β) one_ne_zero one_lt_index
      rw [mul_one] at h
      rw [hsep (omegaIndex ^ β.val) (powβ β hβ), h]
    have bLt : ∀ β : CountableOrdinal, β.val < l.val →
        omegaIndex ^ (ε + omegaIndex ^ β.val) < omegaIndex ^ (ε + omegaIndex ^ l.val) :=
      fun β hβ => (Ordinal.opow_lt_opow_iff_right one_lt_index).2
        ((add_lt_add_iff_left ε).2 (powβ β hβ))
    have condβ : ∀ β : CountableOrdinal, β.val < l.val → ExpCond ε β.val := by
      intro β hβ
      refine ⟨nsep_mono hsep hβ.le, ?_, ?_, lt_trans (bLt β hβ) hb⟩
      · rw [nExp β hβ]
        exact le_max_left _ _
      · rw [nExp β hβ]
        exact (le_max_right _ _).trans (le_max_right _ _)
    have hsupl : ∀ (x : CountableOrdinal) (b : Ordinal.{0}),
        (∀ β : CountableOrdinal, β.val < l.val → (levelTwo fix β H x).val ≤ b) →
        (levelTwo fix l H x).val ≤ b := by
      intro x b Hb
      rw [sup x]
      exact ciSup_le' (fun i => Hb (earlierStage l i) i.property)
    have strict : ∀ β x : CountableOrdinal, β.val < l.val →
        (levelTwo fix β H x).val < (levelTwo fix l H x).val := by
      intro β x hβ
      obtain ⟨β1, hβ1⟩ := countable_mk (β.val + 1)
        ((isSuccLimit_omega 1).add_one_lt (countable_val_lt β))
      have hβ1l : β1.val ≤ l.val := by rw [hβ1]; exact (hl.add_one_lt hβ).le
      exact lt_of_lt_of_le (ltStrict β β1 H hstep.1 hβ1 x) (ltMono β1 l H hstep.1 hβ1l x)
    have hcofl : ∀ τ : Ordinal.{0}, τ < omegaIndex ^ (ε + omegaIndex ^ l.val) →
        ∃ β : CountableOrdinal, β.val < l.val ∧ τ < omegaIndex ^ (ε + omegaIndex ^ β.val) := by
      intro τ hτ
      have hpl : Order.IsSuccLimit (omegaIndex ^ l.val) := Ordinal.isSuccLimit_opow one_lt_index hl
      obtain ⟨c', hc', hτc⟩ := (Ordinal.lt_opow_of_isSuccLimit omegaIndex_ne
        (Ordinal.isSuccLimit_add ε hpl)).1 hτ
      obtain ⟨d, hd, hcd⟩ := (Ordinal.lt_add_iff hpl.ne_bot).1 hc'
      obtain ⟨c'', hc''l, hdc⟩ := (Ordinal.lt_opow_of_isSuccLimit omegaIndex_ne hl).1 hd
      obtain ⟨β, hβ⟩ := countable_mk c'' (hc''l.trans hlΩ)
      refine ⟨β, by rw [hβ]; exact hc''l, ?_⟩
      rw [hβ]
      exact lt_of_lt_of_le hτc (Ordinal.opow_le_opow_right omegaIndex_pos
        (hcd.trans ((add_le_add_iff_left ε).2 hdc.le)))
    have one_le_l : (1 : Ordinal.{0}) ≤ l.val := (Ordinal.one_lt_of_isSuccLimit hl).le
    have hn1l : ∀ β : CountableOrdinal, β.val < l.val →
        coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ β.val)) ≤
          coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ l.val)) := by
      intro β hβ
      rw [norm_opow (ε + omegaIndex ^ β.val) (lt_trans (bLt β hβ) hb),
        norm_opow (ε + omegaIndex ^ l.val) hb, nExp β hβ]
      exact max_le_max le_rfl (max_le hnε (max_le (one_le_l.trans hnl) (hβ.le.trans hnl)))
    have hn2l : ∀ (β : CountableOrdinal) (τ : Ordinal.{0}), β.val < l.val →
        omegaIndex ^ (ε + omegaIndex ^ β.val) ≤ τ → τ < omegaIndex ^ (ε + omegaIndex ^ l.val) →
        coefficientNorm (omegaIndex ^ (ε + omegaIndex ^ β.val)) ≤ coefficientNorm τ := by
      intro β τ hβ hle hτ
      obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := log_split hsep hle hτ hb
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0] at hρ1
        exact absurd hρ1 (not_le.2 (Ordinal.opow_pos β.val omegaIndex_pos))
      have hρΛ : ρ < endpoint := lt_of_lt_of_le hρ2
        ((Ordinal.opow_le_opow_right omegaIndex_pos hlΩ.le).trans top_le_endpoint)
      have hρone : (1 : Ordinal.{0}) ≤ coefficientNorm ρ :=
        (le_max_left _ _).trans (norm_ge_log ρ hρ0 hρΛ)
      rw [norm_opow (ε + omegaIndex ^ β.val) (lt_trans (bLt β hβ) hb), nExp β hβ]
      exact le_trans (max_le_max le_rfl (max_le_max le_rfl
        (max_le hρone (norm_ge_exponent β.val l.val ρ hlΩ hρ1 hρ2)))) hρ3
    have st := stepLimit Z s add mul w one pow fix h1 h2 l
      (fun β => omegaIndex ^ (ε + omegaIndex ^ β.val)) (omegaIndex ^ (ε + omegaIndex ^ l.val))
      (fun β => levelTwo fix β H) (levelTwo fix l H)
      (fun β hβ => (ih β hβ ε H (condβ β hβ) hstep).2.1)
      (fun β hβ => (ih β hβ ε H (condβ β hβ) hstep).2.2)
      bLt hcofl hn1l hn2l strict hsupl (fun x => gl.1.2 x) gl.2.2
    exact ⟨gl, st.1, st.2⟩

#print axioms opWeightSuccessor
#print axioms levelTwoWeight

end LogicLineages.PersistentMarking.ActualCalibrationStep
