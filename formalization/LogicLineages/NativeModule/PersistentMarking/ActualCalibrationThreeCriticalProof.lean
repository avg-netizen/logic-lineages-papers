module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeHierarchyProof

@[expose] public section

/-! Criticality on the function side: successor steps between critical values, closure of the
critical class under limits of critical values, and `N_B`-criticality of every value of a level
`D e`, `e ≥ 1`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

theorem crit_val {N : CountableOrdinal → CountableOrdinal} {Γ : CountableOrdinal} {θ : Ordinal.{0}}
    (h : Critical N Γ θ) : ∃ c : CountableOrdinal, c.val = θ := by
  obtain ⟨α, hα⟩ := h
  exact ⟨_, hα⟩

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem crit_base : Critical (veblenValue fix pow) (baseValue fix pow w) (baseValue fix pow w).val :=
  ⟨zeroValue, congrArg Subtype.val
    (orbit_zero (veblenValue fix pow) (baseValue fix pow w) zeroValue rfl)⟩

theorem crit_ge_base (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) {θ : Ordinal.{0}}
    (hθ : Critical (veblenValue fix pow) (baseValue fix pow w) θ) :
    (baseValue fix pow w).val ≤ θ := by
  obtain ⟨α, hα⟩ := hθ
  have h := orbit_mono (veblenValue fix pow) (baseValue fix pow w) (veblen_infl h1 h2)
    (α := zeroValue) (β := α) (ozl _)
  rw [orbit_zero (veblenValue fix pow) (baseValue fix pow w) zeroValue rfl, hα] at h
  exact h

theorem crit_succ (x : CountableOrdinal)
    (hx : Critical (veblenValue fix pow) (baseValue fix pow w) x.val) :
    Critical (veblenValue fix pow) (baseValue fix pow w) (veblenValue fix pow x).val := by
  obtain ⟨α, hα⟩ := hx
  obtain ⟨α1, hα1⟩ := countable_mk (α.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt α))
  have e : orbit .base (veblenValue fix pow) (baseValue fix pow w) α = x := Subtype.ext hα
  refine ⟨α1, ?_⟩
  rw [orbit_succ (veblenValue fix pow) (baseValue fix pow w) α α1 hα1, e]

/-- Between two critical values there is a full `N_B`-step. -/
theorem crit_step (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (x θ : CountableOrdinal)
    (hx : Critical (veblenValue fix pow) (baseValue fix pow w) x.val)
    (hθ : Critical (veblenValue fix pow) (baseValue fix pow w) θ.val) (h : x.val < θ.val) :
    (veblenValue fix pow x).val ≤ θ.val := by
  have infl := veblen_infl h1 h2
  obtain ⟨α, hα⟩ := hx
  obtain ⟨γ, hγ⟩ := hθ
  have hαγ : α.val < γ.val := by
    by_contra hn
    have m := orbit_mono (veblenValue fix pow) (baseValue fix pow w) infl (not_lt.1 hn)
    rw [hα, hγ] at m
    exact absurd h (not_lt.2 m)
  obtain ⟨α1, hα1⟩ := countable_mk (α.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt α))
  have e : orbit .base (veblenValue fix pow) (baseValue fix pow w) α = x := Subtype.ext hα
  have m := orbit_mono (veblenValue fix pow) (baseValue fix pow w) infl (α := α1) (β := γ)
    (by rw [hα1]; exact Order.add_one_le_of_lt hαγ)
  rw [orbit_succ (veblenValue fix pow) (baseValue fix pow w) α α1 hα1, e, hγ] at m
  exact m

/-- A positive countable ordinal that is approached from below by critical values is critical. -/
theorem critLim (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) (θ : CountableOrdinal) (hpos : 0 < θ.val)
    (H : ∀ y : CountableOrdinal, y.val < θ.val → ∃ c : CountableOrdinal,
      Critical (veblenValue fix pow) (baseValue fix pow w) c.val ∧ y.val < c.val ∧ c.val ≤ θ.val) :
    Critical (veblenValue fix pow) (baseValue fix pow w) θ.val := by
  have infl := veblen_infl h1 h2
  have claim : ∀ γ : CountableOrdinal,
      θ.val ≤ (orbit .base (veblenValue fix pow) (baseValue fix pow w) γ).val →
      Critical (veblenValue fix pow) (baseValue fix pow w) θ.val := by
    refine countable_strong_induction _ (fun γ ih hγ => ?_)
    by_cases hex : ∃ γ' : CountableOrdinal, γ'.val < γ.val ∧
        θ.val ≤ (orbit .base (veblenValue fix pow) (baseValue fix pow w) γ').val
    · obtain ⟨γ', hlt, hle⟩ := hex
      exact ih γ' hlt hle
    · have below : ∀ γ' : CountableOrdinal, γ'.val < γ.val →
          (orbit .base (veblenValue fix pow) (baseValue fix pow w) γ').val < θ.val :=
        fun γ' hlt => not_le.1 (fun hle => hex ⟨γ', hlt, hle⟩)
      rcases hγ.lt_or_eq with hlt | heq
      · exfalso
        rcases countable_cases γ with h0 | ⟨c, hc⟩ | hl
        · obtain ⟨d, hd, -, hdθ⟩ := H zeroValue hpos
          rw [orbit_zero (veblenValue fix pow) (baseValue fix pow w) γ h0] at hlt
          exact absurd ((crit_ge_base h1 h2 hd).trans hdθ) (not_le.2 hlt)
        · have hcγ : c.val < γ.val := by rw [hc]; exact Order.lt_add_one_iff.2 le_rfl
          obtain ⟨d, ⟨δ, hδ⟩, hyd, hdθ⟩ :=
            H (orbit .base (veblenValue fix pow) (baseValue fix pow w) c) (below c hcγ)
          rw [← hδ] at hyd hdθ
          have hcδ : c.val < δ.val := by
            by_contra hn
            exact absurd hyd (not_lt.2
              (orbit_mono (veblenValue fix pow) (baseValue fix pow w) infl (not_lt.1 hn)))
          have hδγ : δ.val < γ.val := by
            by_contra hn
            exact absurd ((orbit_mono (veblenValue fix pow) (baseValue fix pow w) infl
              (not_lt.1 hn)).trans hdθ) (not_le.2 hlt)
          rw [hc] at hδγ
          exact absurd (Order.lt_add_one_iff.1 hδγ) (not_le.2 hcδ)
        · exact absurd (orbit_limit_le (veblenValue fix pow) (baseValue fix pow w) γ hl θ.val
            (fun β hβ => (below β hβ).le)) (not_le.2 hlt)
      · exact ⟨γ, heq.symm⟩
  exact claim θ (orbit_id_le (veblenValue fix pow) (baseValue fix pow w) infl θ)

/-- Every value of a level `D e`, `e ≥ 1`, is critical. -/
theorem level_critical (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) :
    ∀ e : CountableOrdinal, 1 ≤ e.val → ∀ x : CountableOrdinal,
      Critical (veblenValue fix pow) (baseValue fix pow w) (level fix pow e x).val := by
  refine countable_induction _ ?_ ?_ ?_
  · intro e h0 h1e
    rw [h0] at h1e
    exact absurd h1e (not_le.2 zero_lt_one)
  · intro e' e he ih _ x
    obtain ⟨hfix, hx, -⟩ := level_step h1 h2 e' e he x
    have hpos : 0 < (level fix pow e x).val := (ozl _).trans_lt hx
    have hl := enumFix_limit h1 h2 e' (level fix pow e x) hfix hpos
    refine critLim h1 h2 (level fix pow e x) hpos (fun y hy => ?_)
    have hy' : y.val < (orbit .base (level fix pow e') zeroValue (level fix pow e x)).val :=
      lt_of_lt_of_eq hy (congrArg Subtype.val hfix).symm
    obtain ⟨a, ha, hya⟩ := lt_orbit_limit (level fix pow e') zeroValue (level fix pow e x) hl y.val hy'
    by_cases e0 : e'.val = 0
    · have eN : level fix pow e' = veblenValue fix pow := level_zero_eq e' e0
      have big := enumFix_gt_omega h1 h2 e' (level fix pow e x) hfix hpos
      obtain ⟨ω1, hω1⟩ := countable_mk (ω + 1)
        ((hl.add_one_lt big).trans (countable_val_lt (level fix pow e x)))
      have hω1κ : ω1.val < (level fix pow e x).val := by rw [hω1]; exact hl.add_one_lt big
      have hsum := enumFix_add_closed h1 h2 e' (level fix pow e x) hfix hpos ω1 a hω1κ ha
      obtain ⟨γ, hγ⟩ := countable_mk (ω1.val + a.val)
        (hsum.trans (countable_val_lt (level fix pow e x)))
      have cmp := orbitComparison Z s add mul w one pow fix h1 h2 a γ (by rw [hγ, hω1])
      have m := lvEnum_mono h1 h2 e' γ (level fix pow e x) (by rw [hγ]; exact hsum.le)
      rw [hfix] at m
      have e2 : levelEnum fix pow e' γ = orbit .base (veblenValue fix pow) zeroValue γ := by
        show orbit .base (level fix pow e') zeroValue γ = _
        rw [eN]
      rw [e2] at m
      have e3 : orbit .base (level fix pow e') zeroValue a =
          orbit .base (veblenValue fix pow) zeroValue a := by
        rw [eN]
      rw [e3] at hya
      refine ⟨orbit .base (veblenValue fix pow) (baseValue fix pow w) a, ⟨a, rfl⟩, ?_, cmp.trans m⟩
      exact hya.trans_le (orbit_start_mono (veblenValue fix pow) (veblen_monoInfl h1 h2).1
        zeroValue (baseValue fix pow w) (ozl _) a)
    · have e1' : 1 ≤ e'.val := Ordinal.one_le_iff_ne_zero.2 e0
      obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1)
        ((hl.add_one_lt ha).trans (countable_val_lt (level fix pow e x)))
      refine ⟨levelEnum fix pow e' a1, ?_, ?_, ?_⟩
      · rw [lvEnum_succ e' a a1 ha1]
        exact ih e1' (levelEnum fix pow e' a)
      · exact hya.trans (lvEnum_strict h1 h2 e' a a1 (by rw [ha1]; exact Order.lt_add_one_iff.2 le_rfl))
      · have m := lvEnum_mono h1 h2 e' a1 (level fix pow e x)
          (by rw [ha1]; exact (hl.add_one_lt ha).le)
        rw [hfix] at m
        exact m
  · intro l hl ih _ x
    have hml := level_monoInfl h1 h2 l
    have hpos : 0 < (level fix pow l x).val := (ozl _).trans_lt (hml.2 x)
    refine critLim h1 h2 (level fix pow l x) hpos (fun y hy => ?_)
    obtain ⟨β, hβ, hyβ⟩ := lt_level_limit l hl x y.val hy
    have hmax : max β.val 1 < l.val := max_lt hβ (Ordinal.one_lt_of_isSuccLimit hl)
    obtain ⟨m, hm⟩ := countable_mk (max β.val 1) (hmax.trans (countable_val_lt l))
    have hmlt : m.val < l.val := by rw [hm]; exact hmax
    refine ⟨level fix pow m x, ih m hmlt (by rw [hm]; exact le_max_right _ _) x, ?_, ?_⟩
    · exact hyβ.trans_le (level_mono_index h1 h2 β m (by rw [hm]; exact le_max_left _ _) x)
    · exact level_mono_index h1 h2 m l hmlt.le x

end

theorem levelCritical : LevelCritical := by
  intro Z s add mul w one pow fix h1 h2 e he x
  exact level_critical h1 h2 e he x

#print axioms levelCritical
#print axioms crit_step
#print axioms critLim

end LogicLineages.PersistentMarking.ActualCalibrationThree
