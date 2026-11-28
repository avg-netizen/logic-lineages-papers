module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeLevelProof
import LogicLineages.NativeModule.PersistentMarking.ActualCollapseMainProof
import LogicLineages.NativeModule.PersistentMarking.CollapseDiagonalProof
import LogicLineages.NativeModule.PersistentMarking.ActualTowerIndexProof

public section

namespace LogicLineages.PersistentMarking.ActualCalibrationLevelsProof
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualTowerIndex CollapseDiagonal ActualCalibrationLevels Paper16RemainingOrdinalTargets
open scoped Ordinal

theorem semDown_congr : ∀ (m : Nat) (v : Value (tier (m + 1))) (xs ys : Env),
    (∀ j, 1 ≤ j → j ≤ m → xs j = ys j) → semDown m v xs = semDown m v ys := by
  intro m
  induction m with
  | zero =>
    intro v xs ys _
    rfl
  | succ m ih =>
    intro v xs ys h
    show semDown m (v (xs (m + 1))) xs = semDown m (v (ys (m + 1))) ys
    rw [h (m + 1) (by omega) le_rfl]
    exact ih _ xs ys (fun j h1 hj => h j h1 (by omega))

theorem spineValue_congr (l : Nat) (xs ys : Env) (h : ∀ j, 1 ≤ j → j ≤ l + 1 → xs j = ys j)
    (α : CountableOrdinal) : spineValue l xs α = spineValue l ys α := by
  cases l with
  | zero =>
    show orbit (tier 0) (xs 1) zeroValue α = orbit (tier 0) (ys 1) zeroValue α
    rw [h 1 le_rfl (by omega)]
  | succ m =>
    show semDown m (orbit (tier (m + 1)) (xs (m + 2)) (xs (m + 1)) α) xs =
      semDown m (orbit (tier (m + 1)) (ys (m + 2)) (ys (m + 1)) α) ys
    rw [h (m + 2) (by omega) le_rfl, h (m + 1) (by omega) (by omega)]
    exact semDown_congr m _ xs ys (fun j h1 hj => h j h1 (by omega))

theorem down_curry (fix : Value (tier 2)) (pow : Value (tier 1)) (n : Nat) (G : Env → Value (tier 1))
    (hG : ∀ ys zs : Env, (∀ j, 1 ≤ j → j ≤ n → ys j = zs j) → G ys = G zs) :
    ∀ (k : Nat) (xs : Env), (∀ j, k + 2 ≤ j → j ≤ n → xs j = towerEnv fix pow j) →
      downValue fix k (curryEnv (k + 1) G xs) (veblenValue fix pow) = G (towerEnv fix pow) := by
  intro k
  induction k with
  | zero =>
    intro xs hxs
    show G (Function.update xs 1 (veblenValue fix pow)) = G (towerEnv fix pow)
    refine hG _ _ (fun j h1 hj => ?_)
    by_cases hj1 : j = 1
    · subst hj1
      exact (Function.update_self 1 (veblenValue fix pow) xs).trans rfl
    · exact (Function.update_of_ne hj1 _ xs).trans (hxs j (by omega) hj)
  | succ k ih =>
    intro xs hxs
    show downValue fix k (curryEnv (k + 1) G (Function.update xs (k + 2) (towerValue fix k)))
      (veblenValue fix pow) = G (towerEnv fix pow)
    refine ih _ (fun j hk hj => ?_)
    by_cases hjk : j = k + 2
    · subst hjk
      exact (Function.update_self (k + 2) (towerValue fix k) xs).trans rfl
    · exact (Function.update_of_ne hjk _ xs).trans (hxs j (by omega) hj)

theorem exact_DiagonalUnfolding : DiagonalUnfolding := by
  intro fix pow w l
  let G : Env → Value (tier 1) := fun xs => fix (fun α => spineValue l xs α)
  have hG : ∀ ys zs : Env, (∀ j, 1 ≤ j → j ≤ l + 1 → ys j = zs j) → G ys = G zs := by
    intro ys zs h
    exact congrArg (fun g : CountableOrdinal → CountableOrdinal => fix g)
      (funext (spineValue_congr l ys zs h))
  have key := down_curry fix pow (l + 1) G hG l (fun j => valueDefault (tier j))
    (fun j h1 h2 => absurd h2 (by omega))
  exact congrFun key (baseValue fix pow w)

theorem exact_CalibrationStep : CalibrationStep := by
  intro Z s add mul w one pow fix h1 h2 l facts psiLevel
  obtain ⟨strict, baseBelow, Lcont⟩ := facts
  let N := veblenValue fix pow
  let Γ := baseValue fix pow w
  let L : CountableOrdinal → CountableOrdinal := levelDiagonal fix pow l
  obtain ⟨infl, hΓ⟩ := veblenInflationary Z s add mul w one pow fix h1 h2
  have char : CharacterizationP (actualData N Γ) := actualCharacterization N Γ infl hΓ
  obtain ⟨_, critCountable, _, critSup⟩ := criticalFacts N Γ infl hΓ
  obtain ⟨below, normLe, cover⟩ := ActualTowerIndexProof.exact_TowerIndexFacts l
  have bound : ∀ e : CountableOrdinal, towerIndex l e.val ≤ endpoint := fun e =>
    ((below e.val (countable_val_lt e)).trans (exact_BelowEndpoint (l + 2))).le
  let p : CountableOrdinal → ActualIndex := fun e => ⟨towerIndex l e.val, bound e⟩
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
  have Llimit : ∀ lim : CountableOrdinal, Order.IsSuccLimit lim.val → ∀ b : Ordinal.{0},
      (∀ e : CountableOrdinal, e.val < lim.val → (L e).val ≤ b) → (L lim).val ≤ b := by
    intro lim hl b hb
    rw [Lcont lim hl]
    exact ciSup_le' (fun e => hb (earlierStage lim e) e.property)
  have delta : sequenceValue fix pow w (l + 2) = fix L Γ := exact_DiagonalUnfolding fix pow w l
  obtain ⟨fpFix, fpAbove, fpLeast⟩ :=
    fixLeastAbove Z s add mul w one pow fix h1 h2 L Lmono Linfl Lcont Γ
  have noEarly : ∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ Γ.val → L θ ≠ θ := by
    intro θ h1θ hθΓ hfix
    have lt : Γ.val < (L θ).val := baseBelow θ h1θ
    rw [hfix] at lt
    exact absurd hθΓ (not_le.2 lt)
  have H : DiagonalHypotheses (veblenData fix pow w) (actualArgument (l + 2)) p L Γ :=
    { characterization := char
      criticalCountable := critCountable
      criticalAboveBase := critGe
      criticalSup := critSup
      baseAboveOne := hΓ
      strict := strict
      inflationary := Linfl
      limit := Llimit
      noEarlyFixed := noEarly
      below := fun e _ => below e.val (countable_val_lt e)
      norm := fun e h1e => normLe e.val h1e (countable_val_lt e)
      cover := fun η hη e h1e hn => cover η.val e.val hη h1e (countable_val_lt e) hn
      level := fun e h1e hno => psiLevel e h1e hno (bound e) }
  have result := CollapseDiagonalProof.exact_DiagonalCollapse ActualIndex (veblenData fix pow w)
    (actualArgument (l + 2)) p L Γ H (fix L Γ) fpFix fpAbove fpLeast
  rw [delta]
  exact result.symm

theorem exact_AllFromLevels : AllFromLevels := by
  intro levels A n
  match n with
  | 0 =>
    exact (ActualCollapseMain.calibrationFirstInstances A.zero A.successor A.add A.mul A.omega A.one
      A.pow A.fix A.arithmetic A.omegaEquations).1
  | 1 =>
    exact (ActualCollapseMain.calibrationFirstInstances A.zero A.successor A.add A.mul A.omega A.one
      A.pow A.fix A.arithmetic A.omegaEquations).2
  | 2 =>
    exact calibrationTwo A.zero A.successor A.add A.mul A.omega A.one A.pow A.fix A.arithmetic
      A.omegaEquations
  | l + 3 =>
    obtain ⟨facts, psiLevel⟩ := levels A (l + 1) (by omega)
    exact exact_CalibrationStep A.zero A.successor A.add A.mul A.omega A.one A.pow A.fix
      A.arithmetic A.omegaEquations (l + 1) facts psiLevel

#print axioms exact_DiagonalUnfolding
#print axioms exact_CalibrationStep
#print axioms exact_AllFromLevels

end LogicLineages.PersistentMarking.ActualCalibrationLevelsProof
