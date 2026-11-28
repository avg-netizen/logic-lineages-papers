module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePsiTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationTwoProof

@[expose] public section

/-! Norm side of n = 3: the coefficient norm of `Ω^e·c + τ` (`e`, `c` countable, `τ < Ω^e`), its
three consequences for ordinals below `Ω^(e+1)`, and the calculus of `NormSeparated` contexts. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

theorem ozn (x : Ordinal.{0}) : (0 : Ordinal.{0}) ≤ x := not_lt.mp not_lt_zero

theorem omegaIndex_pos : (0 : Ordinal.{0}) < omegaIndex := zero_lt_one.trans one_lt_index

theorem omegaIndex_ne : omegaIndex ≠ 0 := fun h => absurd omegaIndex_pos (by rw [h]; exact lt_irrefl _)

theorem opowIndex_ne (e : Ordinal.{0}) : omegaIndex ^ e ≠ 0 := Ordinal.opow_ne_zero e omegaIndex_ne

theorem argument_three : argument 3 = omegaIndex ^ omegaIndex :=
  (exact_LiteralRecurrence.2.2.2.2 2).trans
    (congrArg (omegaIndex ^ ·) exact_LiteralRecurrence.2.2.2.1)

theorem top_le_endpoint : omegaIndex ^ omegaIndex ≤ endpoint :=
  le_of_eq_of_le argument_three.symm (Ordinal.le_iSup (fun m => argument m) 3)

theorem cnorm_zero : coefficientNorm 0 = 0 := by
  rw [norm_eq, CNF.zero_right]
  rfl

/-- `|Ω^e·c + τ| = max (max c e) |τ|` for countable `e`, `1 ≤ c < Ω`, `τ < Ω^e`. -/
theorem norm_leading (e c τ : Ordinal.{0}) (he : e < omegaIndex) (hc0 : c ≠ 0) (hc : c < omegaIndex)
    (hτ : τ < omegaIndex ^ e) :
    coefficientNorm (omegaIndex ^ e * c + τ) = max (max c e) (coefficientNorm τ) := by
  have hcnf := CNF.opow_mul_add (b := omegaIndex) (e := e) (x := c) (y := τ) one_lt_index hc0 hc hτ
  have hτΛ : τ < endpoint :=
    lt_of_lt_of_le hτ ((Ordinal.opow_le_opow_right omegaIndex_pos he.le).trans top_le_endpoint)
  have tail : ((CNF omegaIndex τ).map (fun p => max p.2
      (if h : p.1 < omegaIndex ^ e * c + τ then coefficientNorm p.1 else 0))).foldr max 0 =
      coefficientNorm τ := by
    rw [norm_eq τ]
    refine congrArg (fun L => List.foldr max 0 L) (List.map_congr_left (fun p hp => ?_))
    have p1 : p.1 < τ := (entry_le hτΛ hp).1
    have p2 : p.1 < omegaIndex ^ e * c + τ := lt_of_lt_of_le p1 le_add_self
    show max p.2 (if h : p.1 < omegaIndex ^ e * c + τ then coefficientNorm p.1 else 0) =
      max p.2 (if h : p.1 < τ then coefficientNorm p.1 else 0)
    rw [dif_pos p1, dif_pos p2]
  have head : (if h : e < omegaIndex ^ e * c + τ then coefficientNorm e else 0) = e := by
    by_cases he0 : e = 0
    · by_cases hlt : e < omegaIndex ^ e * c + τ
      · rw [dif_pos hlt, he0]
        exact cnorm_zero
      · rw [dif_neg hlt]
        exact he0.symm
    · have epos : 0 < e := lt_of_le_of_ne (ozn e) (Ne.symm he0)
      have cpos : 0 < c := lt_of_le_of_ne (ozn c) (Ne.symm hc0)
      have hlt : e < omegaIndex ^ e * c + τ :=
        lt_of_lt_of_le he (((Ordinal.left_le_opow omegaIndex epos).trans
          (Ordinal.le_mul_left (omegaIndex ^ e) cpos)).trans le_self_add)
      rw [dif_pos hlt]
      exact norm_countable e he
  rw [norm_eq (omegaIndex ^ e * c + τ), hcnf]
  simp only [List.map_cons, List.foldr_cons]
  exact congrArg₂ max (congrArg (max c) head) tail

theorem norm_pow (e c : Ordinal.{0}) (he : e < omegaIndex) (hc0 : c ≠ 0) (hc : c < omegaIndex) :
    coefficientNorm (omegaIndex ^ e * c) = max c e := by
  have h := norm_leading e c 0 he hc0 hc (Ordinal.opow_pos e omegaIndex_pos)
  rw [add_zero, cnorm_zero, max_eq_left (ozn (max c e))] at h
  exact h

/-- `τ < Ω^(e+1)` lies below `Ω^e·(b+1)` for a coefficient `b ≤ |τ|`. -/
theorem norm_div_le (e τ : Ordinal.{0}) (he : e < omegaIndex) (hτ : τ < omegaIndex ^ (e + 1)) :
    ∃ b : Ordinal.{0}, b < omegaIndex ∧ b ≤ coefficientNorm τ ∧ τ < omegaIndex ^ e * (b + 1) := by
  have hne := opowIndex_ne e
  have hb : τ / omegaIndex ^ e < omegaIndex := by
    rw [Ordinal.div_lt hne, ← Ordinal.opow_add_one]
    exact hτ
  refine ⟨τ / omegaIndex ^ e, hb, ?_, ?_⟩
  · by_cases hb0 : τ / omegaIndex ^ e = 0
    · rw [hb0]
      exact ozn _
    · have hn := norm_leading e (τ / omegaIndex ^ e) (τ % omegaIndex ^ e) he hb0 hb
        (Ordinal.mod_lt τ hne)
      rw [Ordinal.div_add_mod] at hn
      rw [hn]
      exact (le_max_left _ _).trans (le_max_left _ _)
  · have h := Ordinal.lt_mul_succ_div τ hne
    rw [← Ordinal.add_one_eq_succ] at h
    exact h

/-- `Ω^e·b ≤ τ < Ω^(e+1)` with `b ≥ 1` forces `|τ| ≥ max b e`. -/
theorem norm_ge_of_mul_le (e b τ : Ordinal.{0}) (he : e < omegaIndex) (hb1 : 1 ≤ b)
    (hle : omegaIndex ^ e * b ≤ τ) (hτ : τ < omegaIndex ^ (e + 1)) :
    max b e ≤ coefficientNorm τ := by
  have hne := opowIndex_ne e
  have hc : τ / omegaIndex ^ e < omegaIndex := by
    rw [Ordinal.div_lt hne, ← Ordinal.opow_add_one]
    exact hτ
  have hbc : b ≤ τ / omegaIndex ^ e := (Ordinal.le_div hne).2 hle
  have hc0 : τ / omegaIndex ^ e ≠ 0 := by
    intro h0
    rw [h0] at hbc
    exact absurd (hb1.trans hbc) (not_le.2 zero_lt_one)
  have hn := norm_leading e (τ / omegaIndex ^ e) (τ % omegaIndex ^ e) he hc0 hc
    (Ordinal.mod_lt τ hne)
  rw [Ordinal.div_add_mod] at hn
  rw [hn]
  exact max_le ((hbc.trans (le_max_left _ _)).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))

/-- `Ω^e' ≤ τ < Ω^e` (`e` countable) forces `|τ| ≥ e'`. -/
theorem norm_ge_exponent (e' e τ : Ordinal.{0}) (he : e < omegaIndex) (hle : omegaIndex ^ e' ≤ τ)
    (hτ : τ < omegaIndex ^ e) : e' ≤ coefficientNorm τ := by
  have hτ0 : τ ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact absurd hle (not_le.2 (Ordinal.opow_pos e' omegaIndex_pos))
  have hlog : Ordinal.log omegaIndex τ < e := (Ordinal.lt_opow_iff_log_lt one_lt_index hτ0).1 hτ
  have h1 : e' ≤ Ordinal.log omegaIndex τ := Ordinal.le_log_of_opow_le one_lt_index hle
  have h2 : omegaIndex ^ Ordinal.log omegaIndex τ * 1 ≤ τ := by
    rw [mul_one]
    exact Ordinal.opow_log_le_self omegaIndex hτ0
  have h3 : τ < omegaIndex ^ (Ordinal.log omegaIndex τ + 1) := by
    have h := Ordinal.lt_opow_succ_log_self one_lt_index τ
    rw [← Ordinal.add_one_eq_succ] at h
    exact h
  have h4 := norm_ge_of_mul_le (Ordinal.log omegaIndex τ) 1 τ (hlog.trans he) le_rfl h2 h3
  exact h1.trans ((le_max_right _ _).trans h4)

/-! Contexts. -/

theorem nsep_zero (e : Ordinal.{0}) : NormSeparated 0 e := by
  intro τ _
  rw [zero_add, cnorm_zero]
  exact (max_eq_right (ozn _)).symm

theorem nsep_mono {ζ e e' : Ordinal.{0}} (h : NormSeparated ζ e) (hle : e' ≤ e) :
    NormSeparated ζ e' :=
  fun τ hτ => h τ (lt_of_lt_of_le hτ (Ordinal.opow_le_opow_right omegaIndex_pos hle))

theorem nsep_norm_mul {ζ e c : Ordinal.{0}} (h : NormSeparated ζ (e + 1)) (he : e < omegaIndex)
    (hc0 : c ≠ 0) (hc : c < omegaIndex) :
    coefficientNorm (ζ + omegaIndex ^ e * c) = max (coefficientNorm ζ) (max c e) := by
  have hlt : omegaIndex ^ e * c < omegaIndex ^ (e + 1) := by
    rw [Ordinal.opow_add_one]
    exact mul_lt_mul_of_pos_left hc (Ordinal.opow_pos e omegaIndex_pos)
  rw [h (omegaIndex ^ e * c) hlt, norm_pow e c he hc0 hc]

theorem nsep_step {ζ e c : Ordinal.{0}} (h : NormSeparated ζ (e + 1)) (he : e < omegaIndex)
    (hc : c < omegaIndex) : NormSeparated (ζ + omegaIndex ^ e * c) e := by
  intro τ hτ
  by_cases hc0 : c = 0
  · rw [hc0, mul_zero, add_zero]
    exact h τ (lt_of_lt_of_le hτ (Ordinal.opow_le_opow_right omegaIndex_pos le_self_add))
  · have hlt : omegaIndex ^ e * c + τ < omegaIndex ^ (e + 1) :=
      Ordinal.opow_mul_add_lt_opow hc hτ (Order.lt_add_one_iff.2 le_rfl)
    have e1 : ζ + omegaIndex ^ e * c + τ = ζ + (omegaIndex ^ e * c + τ) := add_assoc _ _ _
    rw [e1, h (omegaIndex ^ e * c + τ) hlt, norm_leading e c τ he hc0 hc hτ,
      nsep_norm_mul h he hc0 hc]
    exact (max_assoc _ _ _).symm

#print axioms norm_leading
#print axioms norm_div_le
#print axioms norm_ge_of_mul_le
#print axioms norm_ge_exponent
#print axioms nsep_step

end LogicLineages.PersistentMarking.ActualCalibrationThree
