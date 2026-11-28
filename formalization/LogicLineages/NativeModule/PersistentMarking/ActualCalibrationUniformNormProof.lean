module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformWeightTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepOrbitProof

@[expose] public section

/-! Norm calculus at arbitrary exponents below `Λ` (the `norm_leading_gen` versions of
`nsep_norm_mul`, `nsep_step`, `norm_div_le`, `norm_ge_of_mul_le`), the separation lemmas for an
exponent context, the chain conditions `CondDown`, and the family lifting: the index hypotheses of
`StepDiagonal`/`StepLimit` pass along `ε ↦ ε + Ω^(·)`, hence along `expDown` and the final `Ω^(·)`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationUniform
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationStep
open scoped Ordinal

/-! Norms at arbitrary exponents. -/

theorem nsepG_norm_mul {ζ e c : Ordinal.{0}} (h : NormSeparated ζ (e + 1))
    (hb : omegaIndex ^ (e + 1) ≤ endpoint) (hc0 : c ≠ 0) (hc : c < omegaIndex) :
    coefficientNorm (ζ + omegaIndex ^ e * c) =
      max (coefficientNorm ζ) (max c (coefficientNorm e)) := by
  have hlt : omegaIndex ^ e * c < omegaIndex ^ (e + 1) := by
    rw [Ordinal.opow_add_one]
    exact mul_lt_mul_of_pos_left hc (Ordinal.opow_pos e omegaIndex_pos)
  have hn := norm_leading_gen e c 0 hc0 hc (Ordinal.opow_pos e omegaIndex_pos)
    (by rw [add_zero]; exact lt_of_lt_of_le hlt hb)
  rw [add_zero, cnorm_zero, max_eq_left (ozl (max c (coefficientNorm e)))] at hn
  rw [h (omegaIndex ^ e * c) hlt, hn]

theorem nsepG_step {ζ e c : Ordinal.{0}} (h : NormSeparated ζ (e + 1))
    (hb : omegaIndex ^ (e + 1) ≤ endpoint) (hc : c < omegaIndex) :
    NormSeparated (ζ + omegaIndex ^ e * c) e := by
  intro τ hτ
  by_cases hc0 : c = 0
  · rw [hc0, mul_zero, add_zero]
    exact h τ (lt_of_lt_of_le hτ (Ordinal.opow_le_opow_right omegaIndex_pos le_self_add))
  · have hlt : omegaIndex ^ e * c + τ < omegaIndex ^ (e + 1) :=
      Ordinal.opow_mul_add_lt_opow hc hτ (Order.lt_add_one_iff.2 le_rfl)
    have e1 : ζ + omegaIndex ^ e * c + τ = ζ + (omegaIndex ^ e * c + τ) := add_assoc _ _ _
    rw [e1, h (omegaIndex ^ e * c + τ) hlt,
      norm_leading_gen e c τ hc0 hc hτ (lt_of_lt_of_le hlt hb), nsepG_norm_mul h hb hc0 hc]
    exact (max_assoc _ _ _).symm

theorem normG_div_le (e τ : Ordinal.{0}) (hb : omegaIndex ^ (e + 1) ≤ endpoint)
    (hτ : τ < omegaIndex ^ (e + 1)) :
    ∃ b : Ordinal.{0}, b < omegaIndex ∧ b ≤ coefficientNorm τ ∧ τ < omegaIndex ^ e * (b + 1) := by
  have hne := opowIndex_ne e
  have hbq : τ / omegaIndex ^ e < omegaIndex := by
    rw [Ordinal.div_lt hne, ← Ordinal.opow_add_one]
    exact hτ
  refine ⟨τ / omegaIndex ^ e, hbq, ?_, ?_⟩
  · by_cases hb0 : τ / omegaIndex ^ e = 0
    · rw [hb0]
      exact ozl _
    · have hn := norm_leading_gen e (τ / omegaIndex ^ e) (τ % omegaIndex ^ e) hb0 hbq
        (Ordinal.mod_lt τ hne) (by rw [Ordinal.div_add_mod]; exact lt_of_lt_of_le hτ hb)
      rw [Ordinal.div_add_mod] at hn
      rw [hn]
      exact (le_max_left _ _).trans (le_max_left _ _)
  · have h := Ordinal.lt_mul_succ_div τ hne
    rw [← Ordinal.add_one_eq_succ] at h
    exact h

theorem normG_ge_of_mul_le (e b τ : Ordinal.{0}) (hb : omegaIndex ^ (e + 1) ≤ endpoint)
    (hb1 : 1 ≤ b) (hle : omegaIndex ^ e * b ≤ τ) (hτ : τ < omegaIndex ^ (e + 1)) :
    max b (coefficientNorm e) ≤ coefficientNorm τ := by
  have hne := opowIndex_ne e
  have hc : τ / omegaIndex ^ e < omegaIndex := by
    rw [Ordinal.div_lt hne, ← Ordinal.opow_add_one]
    exact hτ
  have hbc : b ≤ τ / omegaIndex ^ e := (Ordinal.le_div hne).2 hle
  have hc0 : τ / omegaIndex ^ e ≠ 0 := by
    intro h0
    rw [h0] at hbc
    exact absurd (hb1.trans hbc) (not_le.2 zero_lt_one)
  have hn := norm_leading_gen e (τ / omegaIndex ^ e) (τ % omegaIndex ^ e) hc0 hc
    (Ordinal.mod_lt τ hne) (by rw [Ordinal.div_add_mod]; exact lt_of_lt_of_le hτ hb)
  rw [Ordinal.div_add_mod] at hn
  rw [hn]
  exact max_le ((hbc.trans (le_max_left _ _)).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))

/-! Separation in an exponent context. -/

theorem sep_opow {ε T η : Ordinal.{0}} (hsep : NormSeparated ε T) (hη : η < T)
    (hΛ : omegaIndex ^ η < endpoint) :
    coefficientNorm (ε + omegaIndex ^ η) =
      max (coefficientNorm ε) (max 1 (coefficientNorm η)) := by
  rw [hsep (omegaIndex ^ η) ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 hη), norm_opow η hΛ]

theorem sep_sub {ε T τ : Ordinal.{0}} (hsep : NormSeparated ε T) (hle : ε ≤ τ)
    (hτ : τ < ε + omegaIndex ^ T) :
    τ - ε < omegaIndex ^ T ∧
      coefficientNorm τ = max (coefficientNorm ε) (coefficientNorm (τ - ε)) := by
  have hδ : τ - ε < omegaIndex ^ T := (Ordinal.sub_lt_of_le hle).2 hτ
  have h := hsep (τ - ε) hδ
  rw [Ordinal.add_sub_cancel_of_le hle] at h
  exact ⟨hδ, h⟩

/-- An index in `[ε + Ω^η, ε + Ω^T)` has a leading exponent `ρ ∈ [η, T)` above `ε`, dominated in norm. -/
theorem sep_ge {ε T η τ : Ordinal.{0}} (hsep : NormSeparated ε T)
    (hΛ : ε + omegaIndex ^ T ≤ endpoint) (hle : ε + omegaIndex ^ η ≤ τ)
    (hτ : τ < ε + omegaIndex ^ T) :
    ∃ ρ : Ordinal.{0}, η ≤ ρ ∧ ρ < T ∧
      max (coefficientNorm ε) (max 1 (coefficientNorm ρ)) ≤ coefficientNorm τ := by
  have hετ : ε ≤ τ := le_self_add.trans hle
  obtain ⟨hδ, hn⟩ := sep_sub hsep hετ hτ
  have hδle : omegaIndex ^ η ≤ τ - ε := (Ordinal.le_sub_of_le hετ).2 hle
  have hδ0 : τ - ε ≠ 0 := by
    intro h0
    rw [h0] at hδle
    exact absurd hδle (not_le.2 (Ordinal.opow_pos η omegaIndex_pos))
  have hδΛ : τ - ε < endpoint := lt_of_lt_of_le hδ (le_add_self.trans hΛ)
  refine ⟨Ordinal.log omegaIndex (τ - ε), Ordinal.le_log_of_opow_le one_lt_index hδle,
    (Ordinal.lt_opow_iff_log_lt one_lt_index hδ0).1 hδ, ?_⟩
  rw [hn]
  exact max_le_max le_rfl (norm_ge_log (τ - ε) hδ0 hδΛ)

/-- An index below `ε + Ω^T` lies below `ε + Ω^η` for every `η` above some `ρ < T` of smaller norm. -/
theorem sep_lt {ε T τ : Ordinal.{0}} (hsep : NormSeparated ε T)
    (hΛ : ε + omegaIndex ^ T ≤ endpoint) (hT : 0 < T) (hτ : τ < ε + omegaIndex ^ T) :
    ∃ ρ : Ordinal.{0}, ρ < T ∧ coefficientNorm ρ ≤ coefficientNorm τ ∧
      ∀ η : Ordinal.{0}, ρ < η → τ < ε + omegaIndex ^ η := by
  rcases lt_or_ge ε τ with hlt | hge
  · obtain ⟨hδ, hn⟩ := sep_sub hsep hlt.le hτ
    have hcancel : ε + (τ - ε) = τ := Ordinal.add_sub_cancel_of_le hlt.le
    have hδ0 : τ - ε ≠ 0 := by
      intro h0
      have h := hcancel
      rw [h0, add_zero] at h
      exact absurd h (ne_of_lt hlt)
    have hδΛ : τ - ε < endpoint := lt_of_lt_of_le hδ (le_add_self.trans hΛ)
    refine ⟨Ordinal.log omegaIndex (τ - ε),
      (Ordinal.lt_opow_iff_log_lt one_lt_index hδ0).1 hδ, ?_, fun η hη => ?_⟩
    · rw [hn]
      exact ((le_max_right _ _).trans (norm_ge_log (τ - ε) hδ0 hδΛ)).trans (le_max_right _ _)
    · have hs : τ - ε < omegaIndex ^ (Ordinal.log omegaIndex (τ - ε) + 1) := by
        have h := Ordinal.lt_opow_succ_log_self one_lt_index (τ - ε)
        rw [← Ordinal.add_one_eq_succ] at h
        exact h
      have h2 : τ - ε < omegaIndex ^ η :=
        lt_of_lt_of_le hs (Ordinal.opow_le_opow_right omegaIndex_pos (Order.add_one_le_of_lt hη))
      exact lt_of_eq_of_lt hcancel.symm ((add_lt_add_iff_left ε).2 h2)
  · refine ⟨0, hT, by rw [cnorm_zero]; exact ozl _, fun η _ => ?_⟩
    have h := (add_lt_add_iff_left ε).2 (Ordinal.opow_pos η omegaIndex_pos)
    rw [add_zero] at h
    exact lt_of_le_of_lt hge h

/-! One lifting step `η ↦ ε + Ω^η`. -/

theorem lift_one_le {ε T : Ordinal.{0}} (hΛ : ε + omegaIndex ^ T < endpoint) :
    (1 : Ordinal.{0}) ≤ coefficientNorm (ε + omegaIndex ^ T) := by
  have h0 : ε + omegaIndex ^ T ≠ 0 := by
    intro h
    have hp : omegaIndex ^ T ≤ ε + omegaIndex ^ T := le_add_self
    rw [h] at hp
    exact absurd hp (not_le.2 (Ordinal.opow_pos T omegaIndex_pos))
  exact (le_max_left _ _).trans (norm_ge_log _ h0 hΛ)

theorem diagFam_lift {ε T : Ordinal.{0}} {η : CountableOrdinal → Ordinal.{0}} (hF : DiagFam η T)
    (hS : ExpSep ε T) (hΛ : ε + omegaIndex ^ T < endpoint) :
    DiagFam (fun a => ε + omegaIndex ^ η a) (ε + omegaIndex ^ T) := by
  obtain ⟨hlt, hcof, hn1, hn2⟩ := hF
  obtain ⟨hsep, hnε, hnT⟩ := hS
  have hT0 : 0 < T := lt_of_le_of_lt (ozl _) (hlt zeroValue)
  have hΛT : omegaIndex ^ T < endpoint := lt_of_le_of_lt le_add_self hΛ
  have nA : ∀ a : CountableOrdinal, coefficientNorm (ε + omegaIndex ^ η a) =
      max (coefficientNorm ε) (max 1 (coefficientNorm (η a))) := fun a =>
    sep_opow hsep (hlt a) (lt_trans ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (hlt a)) hΛT)
  have n1 := lift_one_le hΛ
  refine ⟨fun a => (add_lt_add_iff_left ε).2 ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (hlt a)),
    fun τ hτ => ?_, fun a ha => ?_, fun a τ ha hle hτ => ?_⟩
  · obtain ⟨ρ, hρT, hρn, hρ⟩ := sep_lt hsep hΛ.le hT0 hτ
    obtain ⟨a, b, hb, han, hρb⟩ := hcof ρ hρT
    exact ⟨a, b, hb, han.trans hρn, hρ (η b) hρb⟩
  · show coefficientNorm (ε + omegaIndex ^ η a) ≤ max (coefficientNorm (ε + omegaIndex ^ T)) a.val
    rw [nA a]
    exact max_le (hnε.trans (le_max_left _ _))
      (max_le (n1.trans (le_max_left _ _)) ((hn1 a ha).trans (max_le_max hnT le_rfl)))
  · obtain ⟨ρ, h1, h2, h3⟩ := sep_ge hsep hΛ.le hle hτ
    show coefficientNorm (ε + omegaIndex ^ η a) ≤ coefficientNorm τ
    rw [nA a]
    exact le_trans (max_le_max le_rfl (max_le_max le_rfl (hn2 a ρ ha h1 h2))) h3

theorem limFam_lift {ε T : Ordinal.{0}} {l : CountableOrdinal} {η : CountableOrdinal → Ordinal.{0}}
    (hl0 : 0 < l.val) (hF : LimFam l η T) (hS : ExpSep ε T)
    (hΛ : ε + omegaIndex ^ T < endpoint) :
    LimFam l (fun β => ε + omegaIndex ^ η β) (ε + omegaIndex ^ T) := by
  obtain ⟨hlt, hcof, hn1, hn2⟩ := hF
  obtain ⟨hsep, hnε, hnT⟩ := hS
  have hT0 : 0 < T := lt_of_le_of_lt (ozl _) (hlt zeroValue hl0)
  have hΛT : omegaIndex ^ T < endpoint := lt_of_le_of_lt le_add_self hΛ
  have nA : ∀ β : CountableOrdinal, β.val < l.val → coefficientNorm (ε + omegaIndex ^ η β) =
      max (coefficientNorm ε) (max 1 (coefficientNorm (η β))) := fun β hβ =>
    sep_opow hsep (hlt β hβ)
      (lt_trans ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (hlt β hβ)) hΛT)
  have n1 := lift_one_le hΛ
  refine ⟨fun β hβ => (add_lt_add_iff_left ε).2
      ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 (hlt β hβ)),
    fun τ hτ => ?_, fun β hβ => ?_, fun β τ hβ hle hτ => ?_⟩
  · obtain ⟨ρ, hρT, -, hρ⟩ := sep_lt hsep hΛ.le hT0 hτ
    obtain ⟨β, hβ, hρβ⟩ := hcof ρ hρT
    exact ⟨β, hβ, hρ (η β) hρβ⟩
  · show coefficientNorm (ε + omegaIndex ^ η β) ≤ coefficientNorm (ε + omegaIndex ^ T)
    rw [nA β hβ]
    exact max_le hnε (max_le n1 ((hn1 β hβ).trans hnT))
  · obtain ⟨ρ, h1, h2, h3⟩ := sep_ge hsep hΛ.le hle hτ
    show coefficientNorm (ε + omegaIndex ^ η β) ≤ coefficientNorm τ
    rw [nA β hβ]
    exact le_trans (max_le_max le_rfl (max_le_max le_rfl (hn2 β ρ hβ h1 h2))) h3

/-! The chain. -/

theorem le_expDown : ∀ (k : Nat) (ss : Nat → Ordinal.{0}) (σ : Ordinal.{0}),
    σ ≤ expDown k ss σ := by
  intro k
  induction k with
  | zero =>
    intro ss σ
    exact le_rfl
  | succ k ih =>
    intro ss σ
    exact ((Ordinal.right_le_opow σ one_lt_index).trans le_add_self).trans
      (ih ss (ss (k + 1) + omegaIndex ^ σ))

theorem condDown_bound : ∀ (k : Nat) (ss : Nat → Ordinal.{0}) (σ : Ordinal.{0}),
    CondDown k ss σ → omegaIndex ^ expDown k ss σ < endpoint := by
  intro k
  induction k with
  | zero =>
    intro ss σ h
    exact h
  | succ k ih =>
    intro ss σ h
    have h' : ExpSep (ss (k + 1)) σ ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ σ) := h
    exact ih ss _ h'.2

theorem condDown_opow_lt (k : Nat) (ss : Nat → Ordinal.{0}) (σ : Ordinal.{0})
    (h : CondDown k ss σ) : omegaIndex ^ σ < endpoint :=
  lt_of_le_of_lt (Ordinal.opow_le_opow_right omegaIndex_pos (le_expDown k ss σ))
    (condDown_bound k ss σ h)

theorem condDown_lt (k : Nat) (ss : Nat → Ordinal.{0}) (σ : Ordinal.{0})
    (h : CondDown k ss σ) : σ < endpoint :=
  lt_of_le_of_lt (Ordinal.right_le_opow σ one_lt_index) (condDown_opow_lt k ss σ h)

theorem expSep_mono {ε σ σ' : Ordinal.{0}} (hle : σ' ≤ σ) (hΛ : omegaIndex ^ σ < endpoint)
    (h : ExpSep ε σ) : ExpSep ε σ' := by
  rcases hle.eq_or_lt with heq | hlt
  · rw [heq]
    exact h
  · obtain ⟨hsep, -, -⟩ := h
    have hΛ' : omegaIndex ^ σ' < endpoint :=
      lt_trans ((Ordinal.opow_lt_opow_iff_right one_lt_index).2 hlt) hΛ
    refine ⟨nsep_mono hsep hle, ?_, ?_⟩
    · rw [sep_opow hsep hlt hΛ']
      exact le_max_left _ _
    · rw [sep_opow hsep hlt hΛ']
      exact (le_max_right _ _).trans (le_max_right _ _)

theorem condDown_mono : ∀ (k : Nat) (ss : Nat → Ordinal.{0}) (σ σ' : Ordinal.{0}),
    σ' ≤ σ → CondDown k ss σ → CondDown k ss σ' := by
  intro k
  induction k with
  | zero =>
    intro ss σ σ' hle h
    have h' : omegaIndex ^ σ < endpoint := h
    show omegaIndex ^ σ' < endpoint
    exact lt_of_le_of_lt (Ordinal.opow_le_opow_right omegaIndex_pos hle) h'
  | succ k ih =>
    intro ss σ σ' hle h
    have h' : ExpSep (ss (k + 1)) σ ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ σ) := h
    show ExpSep (ss (k + 1)) σ' ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ σ')
    exact ⟨expSep_mono hle (condDown_opow_lt (k + 1) ss σ h) h'.1,
      ih ss _ _ ((add_le_add_iff_left _).2 (Ordinal.opow_le_opow_right omegaIndex_pos hle)) h'.2⟩

theorem expSep_zero (E : Ordinal.{0}) (hΛ : omegaIndex ^ E < endpoint) : ExpSep 0 E := by
  refine ⟨nsep_zero E, ?_, ?_⟩
  · rw [cnorm_zero]
    exact ozl _
  · rw [zero_add, norm_opow E hΛ]
    exact le_max_right _ _

theorem diagFam_expDown : ∀ (k : Nat) (ss : Nat → Ordinal.{0})
    (η : CountableOrdinal → Ordinal.{0}) (T : Ordinal.{0}),
    DiagFam η T → CondDown k ss T → DiagFam (fun a => expDown k ss (η a)) (expDown k ss T) := by
  intro k
  induction k with
  | zero =>
    intro ss η T hF _
    exact hF
  | succ k ih =>
    intro ss η T hF hc
    have hc' : ExpSep (ss (k + 1)) T ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ T) := hc
    exact ih ss (fun a => ss (k + 1) + omegaIndex ^ η a) (ss (k + 1) + omegaIndex ^ T)
      (diagFam_lift hF hc'.1 (condDown_lt k ss _ hc'.2)) hc'.2

theorem limFam_expDown : ∀ (k : Nat) (ss : Nat → Ordinal.{0}) (l : CountableOrdinal)
    (η : CountableOrdinal → Ordinal.{0}) (T : Ordinal.{0}), 0 < l.val →
    LimFam l η T → CondDown k ss T → LimFam l (fun β => expDown k ss (η β)) (expDown k ss T) := by
  intro k
  induction k with
  | zero =>
    intro ss l η T _ hF _
    exact hF
  | succ k ih =>
    intro ss l η T hl0 hF hc
    have hc' : ExpSep (ss (k + 1)) T ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ T) := hc
    exact ih ss l (fun β => ss (k + 1) + omegaIndex ^ η β) (ss (k + 1) + omegaIndex ^ T) hl0
      (limFam_lift hl0 hF hc'.1 (condDown_lt k ss _ hc'.2)) hc'.2

theorem familyLifting : FamilyLifting := by
  refine ⟨fun k ss η T hF hc => ?_, fun k ss l η T hl0 hF hc => ?_⟩
  · have hΛ := condDown_bound k ss T hc
    have h := diagFam_lift (diagFam_expDown k ss η T hF hc) (expSep_zero _ hΛ)
      (by rw [zero_add]; exact hΛ)
    simp only [zero_add] at h
    exact h
  · have hΛ := condDown_bound k ss T hc
    have h := limFam_lift hl0 (limFam_expDown k ss l η T hl0 hF hc) (expSep_zero _ hΛ)
      (by rw [zero_add]; exact hΛ)
    simp only [zero_add] at h
    exact h

/-! The base families `a ↦ σ' + Ω^σ·a`. -/

theorem diagFam_base {σ σ' : Ordinal.{0}} (hS : ExpSep σ' (σ + 1))
    (hσ : coefficientNorm σ ≤ coefficientNorm (σ + 1))
    (hΛ : σ' + omegaIndex ^ (σ + 1) < endpoint) :
    DiagFam (fun a : CountableOrdinal => σ' + omegaIndex ^ σ * a.val)
      (σ' + omegaIndex ^ (σ + 1)) := by
  obtain ⟨hsep, hnε, hnT⟩ := hS
  have hb : omegaIndex ^ (σ + 1) ≤ endpoint := le_add_self.trans hΛ.le
  have hpowpos : 0 < omegaIndex ^ σ := Ordinal.opow_pos σ omegaIndex_pos
  have mulLt : ∀ a : CountableOrdinal, omegaIndex ^ σ * a.val < omegaIndex ^ (σ + 1) := by
    intro a
    rw [Ordinal.opow_add_one]
    exact mul_lt_mul_of_pos_left (countable_val_lt a) hpowpos
  have nExp : ∀ a : CountableOrdinal, a.val ≠ 0 →
      coefficientNorm (σ' + omegaIndex ^ σ * a.val) =
        max (coefficientNorm σ') (max a.val (coefficientNorm σ)) :=
    fun a ha0 => nsepG_norm_mul hsep hb ha0 (countable_val_lt a)
  refine ⟨fun a => (add_lt_add_iff_left σ').2 (mulLt a), fun τ hτ => ?_, fun a ha1 => ?_,
    fun a τ ha1 hle hτ => ?_⟩
  · obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
    have ho1' : o1.val = zeroValue.val + 1 := ho1.trans (zero_add (1 : Ordinal.{0})).symm
    rcases lt_or_ge τ σ' with hlt | hge
    · refine ⟨zeroValue, o1, ho1', ozl _, ?_⟩
      show τ < σ' + omegaIndex ^ σ * o1.val
      exact lt_of_lt_of_le hlt le_self_add
    · obtain ⟨hδ, hn⟩ := sep_sub hsep hge hτ
      obtain ⟨b0, hb0Ω, hb0n, hδb⟩ := normG_div_le σ (τ - σ') hb hδ
      obtain ⟨a, ha⟩ := countable_mk b0 hb0Ω
      obtain ⟨b, hb'⟩ := countable_mk (a.val + 1)
        ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
      refine ⟨a, b, hb', ?_, ?_⟩
      · rw [ha, hn]
        exact hb0n.trans (le_max_right _ _)
      · show τ < σ' + omegaIndex ^ σ * b.val
        rw [hb', ha]
        exact lt_of_eq_of_lt (Ordinal.add_sub_cancel_of_le hge).symm
          ((add_lt_add_iff_left σ').2 hδb)
  · have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    show coefficientNorm (σ' + omegaIndex ^ σ * a.val) ≤
      max (coefficientNorm (σ' + omegaIndex ^ (σ + 1))) a.val
    rw [nExp a ha0]
    exact max_le (hnε.trans (le_max_left _ _))
      (max_le (le_max_right _ _) ((hσ.trans hnT).trans (le_max_left _ _)))
  · have ha0 : a.val ≠ 0 := fun h => absurd ha1 (by rw [h]; exact not_le.2 zero_lt_one)
    have hge : σ' ≤ τ := le_self_add.trans hle
    obtain ⟨hδ, hn⟩ := sep_sub hsep hge hτ
    have hδle : omegaIndex ^ σ * a.val ≤ τ - σ' := (Ordinal.le_sub_of_le hge).2 hle
    show coefficientNorm (σ' + omegaIndex ^ σ * a.val) ≤ coefficientNorm τ
    rw [nExp a ha0, hn]
    exact max_le_max le_rfl (normG_ge_of_mul_le σ a.val (τ - σ') hb ha1 hδle hδ)

theorem limFam_base {σ σ' : Ordinal.{0}} (hsep : NormSeparated σ' (σ + 1))
    (hb : omegaIndex ^ (σ + 1) ≤ endpoint) (l : CountableOrdinal)
    (hl : Order.IsSuccLimit l.val) :
    LimFam l (fun β : CountableOrdinal => σ' + omegaIndex ^ σ * β.val)
      (σ' + omegaIndex ^ σ * l.val) := by
  have hpowpos : 0 < omegaIndex ^ σ := Ordinal.opow_pos σ omegaIndex_pos
  have mulLt : ∀ a : CountableOrdinal, omegaIndex ^ σ * a.val < omegaIndex ^ (σ + 1) := by
    intro a
    rw [Ordinal.opow_add_one]
    exact mul_lt_mul_of_pos_left (countable_val_lt a) hpowpos
  have nExp : ∀ a : CountableOrdinal, a.val ≠ 0 →
      coefficientNorm (σ' + omegaIndex ^ σ * a.val) =
        max (coefficientNorm σ') (max a.val (coefficientNorm σ)) :=
    fun a ha0 => nsepG_norm_mul hsep hb ha0 (countable_val_lt a)
  have hl0 : l.val ≠ 0 := hl.ne_bot
  have nLe : ∀ β : CountableOrdinal, β.val ≤ l.val →
      coefficientNorm (σ' + omegaIndex ^ σ * β.val) ≤
        coefficientNorm (σ' + omegaIndex ^ σ * l.val) := by
    intro β hβ
    rw [nExp l hl0]
    by_cases hβ0 : β.val = 0
    · rw [hβ0, mul_zero, add_zero]
      exact le_max_left _ _
    · rw [nExp β hβ0]
      exact max_le_max le_rfl (max_le_max hβ le_rfl)
  refine ⟨fun β hβ => (add_lt_add_iff_left σ').2 (mul_lt_mul_of_pos_left hβ hpowpos),
    fun τ hτ => ?_, fun β hβ => nLe β hβ.le, fun β τ hβ hle hτ => ?_⟩
  · have hmullim : Order.IsSuccLimit (omegaIndex ^ σ * l.val) :=
      Ordinal.isSuccLimit_mul_right hpowpos hl
    obtain ⟨d, hd, hcd⟩ := (Ordinal.lt_add_iff hmullim.ne_bot).1 hτ
    obtain ⟨c'', hc''l, hdc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit hl).1 hd
    obtain ⟨β, hβ⟩ := countable_mk c'' (hc''l.trans (countable_val_lt l))
    refine ⟨β, by rw [hβ]; exact hc''l, ?_⟩
    show τ < σ' + omegaIndex ^ σ * β.val
    rw [hβ]
    exact lt_of_le_of_lt hcd ((add_lt_add_iff_left σ').2 hdc)
  · have hge : σ' ≤ τ := le_self_add.trans hle
    have hτ' : τ < σ' + omegaIndex ^ (σ + 1) :=
      lt_trans hτ ((add_lt_add_iff_left σ').2 (mulLt l))
    obtain ⟨hδ, hn⟩ := sep_sub hsep hge hτ'
    have hδle : omegaIndex ^ σ * β.val ≤ τ - σ' := (Ordinal.le_sub_of_le hge).2 hle
    show coefficientNorm (σ' + omegaIndex ^ σ * β.val) ≤ coefficientNorm τ
    by_cases hβ0 : β.val = 0
    · rw [hβ0, mul_zero, add_zero, hn]
      exact le_max_left _ _
    · rw [nExp β hβ0, hn]
      exact max_le_max le_rfl (normG_ge_of_mul_le σ β.val (τ - σ') hb
        (Order.one_le_iff_ne_zero.2 hβ0) hδle hδ)

#print axioms familyLifting
#print axioms diagFam_base
#print axioms limFam_base

end LogicLineages.PersistentMarking.ActualCalibrationUniform
