module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeReductionTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeLevelProof
import LogicLineages.NativeModule.PersistentMarking.CollapseDiagonalProof

public section

namespace LogicLineages.PersistentMarking.ActualCalibrationThreeReductionProof
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open CollapseDiagonal ActualCalibrationThreeReduction
open scoped Ordinal

theorem exact_PowerIndexFacts : PowerIndexFacts := by
  have top3 : argument 3 = omegaIndex ^ omegaIndex :=
    (exact_LiteralRecurrence.2.2.2.2 2).trans (congrArg (omegaIndex ^ ·) exact_LiteralRecurrence.2.2.2.1)
  refine ⟨fun e => ?_, fun e h1 => ?_, fun η hη e h1 hn => ?_⟩
  · show omegaIndex ^ e.val < argument 3
    rw [top3]
    exact (opow_lt_opow_iff_right one_lt_index).2 (show e.val < omegaIndex from countable_val_lt e)
  · show coefficientNorm (omegaIndex ^ e.val) ≤ e.val
    rw [norm_eq, cnf_power]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    refine max_le (max_le h1 ?_) (zero_le_one.trans h1)
    split
    · exact (norm_countable e.val (countable_val_lt e)).le
    · exact zero_le_one.trans h1
  · show η.val < omegaIndex ^ e.val
    have hη3 : η.val < argument 3 := hη
    have hηtop : η.val < omegaIndex ^ omegaIndex := by rwa [top3] at hη3
    have hn' : coefficientNorm η.val < e.val := hn
    rcases eq_or_ne η.val 0 with h0 | h0
    · rw [h0]
      exact opow_pos _ (zero_lt_one.trans one_lt_index)
    · have logLt : log omegaIndex η.val < omegaIndex := (lt_opow_iff_log_lt one_lt_index h0).1 hηtop
      have mem : (log omegaIndex η.val, η.val / omegaIndex ^ log omegaIndex η.val) ∈
          CNF omegaIndex η.val := by
        rw [CNF.ne_zero h0]
        exact List.mem_cons_self
      have hΛ : η.val < endpoint := hη3.trans (exact_BelowEndpoint 3)
      have he : coefficientNorm (log omegaIndex η.val) ≤ coefficientNorm η.val := (entry_le hΛ mem).2.2
      rw [norm_countable _ (show log omegaIndex η.val < ω₁ from logLt)] at he
      exact (lt_opow_iff_log_lt one_lt_index h0).2 (lt_of_le_of_lt he hn')

theorem exact_ThreeFromLevelFacts : ThreeFromLevelFacts := by
  intro Z s add mul w one pow fix h1 h2 strict baseBelow psiLevel
  let N := veblenValue fix pow
  let Γ := baseValue fix pow w
  let L : CountableOrdinal → CountableOrdinal := fun α => level fix pow α zeroValue
  obtain ⟨infl, hΓ⟩ := veblenInflationary Z s add mul w one pow fix h1 h2
  have char : CharacterizationP (actualData N Γ) := actualCharacterization N Γ infl hΓ
  obtain ⟨_, critCountable, _, critSup⟩ := criticalFacts N Γ infl hΓ
  obtain ⟨below, normLe, cover⟩ := exact_PowerIndexFacts
  have eqs := orbitEquations (tier 1) (towerValue fix 0) N
  have critGe : ∀ θ, Critical N Γ θ → Γ.val ≤ θ := by
    rintro θ ⟨α, rfl⟩
    let z := mkCountable 0 zero_lt_omegaOne
    have le := orbit_mono N Γ infl (α := z) (β := α)
      (show (0 : Ordinal.{0}) ≤ α.val from not_lt.mp not_lt_zero)
    rwa [orbit_zero N Γ z rfl] at le
  have Linfl : ∀ x : CountableOrdinal, x.val ≤ (L x).val := by
    refine countable_strong_induction _ (fun x ih => ?_)
    by_contra hcon
    have lt : (L x).val < x.val := not_le.1 hcon
    exact absurd (ih (L x) lt) (not_le.2 (strict (L x) x lt))
  have Lmono : ∀ x y : CountableOrdinal, x.val ≤ y.val → (L x).val ≤ (L y).val := by
    intro x y hxy
    rcases hxy.lt_or_eq with h | h
    · exact (strict x y h).le
    · have eq : x = y := Subtype.ext h
      rw [eq]
  have Lcont : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val →
      (L l).val = ⨆ e : EarlierStages l, (L (earlierStage l e)).val :=
    fun l hl => eqs.2.2 l hl zeroValue
  have Llimit : ∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ b : Ordinal.{0},
      (∀ e : CountableOrdinal, e.val < l.val → (L e).val ≤ b) → (L l).val ≤ b := by
    intro l hl b hb
    rw [Lcont l hl]
    exact ciSup_le' (fun e => hb (earlierStage l e) e.property)
  have delta : sequenceValue fix pow w 3 = fix L Γ :=
    congrFun (NativeTowerProof.towerValue_one fix (towerValue fix 0) N) Γ
  obtain ⟨fpFix, fpAbove, fpLeast⟩ :=
    fixLeastAbove Z s add mul w one pow fix h1 h2 L Lmono Linfl Lcont Γ
  have noEarly : ∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ Γ.val → L θ ≠ θ := by
    intro θ h1θ hθΓ hfix
    have lt : Γ.val < (L θ).val := baseBelow θ h1θ
    rw [hfix] at lt
    exact absurd hθΓ (not_le.2 lt)
  have H : DiagonalHypotheses (veblenData fix pow w) (actualArgument 3) powerIndex L Γ :=
    { characterization := char
      criticalCountable := critCountable
      criticalAboveBase := critGe
      criticalSup := critSup
      baseAboveOne := hΓ
      strict := strict
      inflationary := Linfl
      limit := Llimit
      noEarlyFixed := noEarly
      below := fun e _ => below e
      norm := normLe
      cover := cover
      level := psiLevel }
  have result := CollapseDiagonalProof.exact_DiagonalCollapse ActualIndex (veblenData fix pow w)
    (actualArgument 3) powerIndex L Γ H (fix L Γ) fpFix fpAbove fpLeast
  rw [delta]
  exact result.symm

theorem exact_ThreeFromPower : ThreeFromPower := by
  intro facts power Z s add mul w one pow fix h1 h2
  obtain ⟨strict, baseBelow⟩ := facts Z s add mul w one pow fix h1 h2
  exact exact_ThreeFromLevelFacts Z s add mul w one pow fix h1 h2 strict baseBelow
    (power Z s add mul w one pow fix h1 h2)

#print axioms exact_PowerIndexFacts
#print axioms exact_ThreeFromLevelFacts
#print axioms exact_ThreeFromPower

end LogicLineages.PersistentMarking.ActualCalibrationThreeReductionProof
