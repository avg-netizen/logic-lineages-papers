module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightEffectiveTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalHeightEffectiveProof
open Spine NativeReduction NativeIteratorStrictTargets NativeIndexedCarrierTargets NativeRankTargets
open NativeTowerTargets NativeTowerSequenceTargets ConditionalTowerCofinality ExternalOrdinalInterfaceTargets
open ConditionalHeightTargets ConditionalHeightProof ConditionalHeightEffectiveTargets

universe u

/-! (a) The explicit recursion of the family (definitional equations of #1462/#1458). -/

theorem sequenceTerm_eq_zero : sequenceTerm 0 = baseTerm := rfl
theorem sequenceTerm_eq_one : sequenceTerm 1 = app indexType indexType veblenTerm baseTerm := rfl
theorem sequenceTerm_eq_add_two (l : Nat) :
    sequenceTerm (l + 2) =
      app indexType indexType (app (tierType 1) (tierType 1) (downTerm l (towerB l)) veblenTerm) baseTerm :=
  rfl
theorem downTerm_eq_zero (v : Expr) : downTerm 0 v = v := rfl
theorem downTerm_eq_succ (k : Nat) (v : Expr) :
    downTerm (k + 1) v = downTerm k (app (tierType (k+2)) (tierType (k+2)) v (towerB k)) := rfl
theorem towerB_eq (l : Nat) :
    towerB l = binders (l + 1) (fixBody NativeOrdinalExponentialTargets.ordinalFix l boundSlots) := rfl

theorem effectiveFamily {I : Type u} [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0})
    (calibration : Calibration D) (tower : TowerHypotheses D) (endpoint : BHIdentification D BH)
    (upper : UpperBound BH) : EffectiveCofinalFamily BH := by
  intro S wfFull wfNative
  have ranks := towerRanks D calibration S wfNative
  let t : ℕ → ClosedNativeTerm S indexType := fun n =>
    ⟨sequenceTerm n, by
      obtain ⟨u, uv, _⟩ := ranks n
      rw [← uv]
      exact u.property⟩
  have below : ∀ n, D.psi (D.a n) ≤ nativeRank (wfNative.apply (t n)) := by
    intro n
    obtain ⟨u, uv, hu⟩ := ranks n
    have e : u = t n := Subtype.ext uv
    rw [← e]
    exact hu
  have lub : IsLUB (Set.range (fun n => D.psi (D.a n))) (⨆ n, D.psi (D.a n)) :=
    isLUB_ciSup (Ordinal.bddAbove_range _)
  have cofinal := conditionalTowerCofinality I Ordinal.{0} D BH tower endpoint _ lub
  refine ⟨t, fun n => rfl, ?_, ?_, ?_⟩
  · intro β hβ
    rw [← cofinal.2] at hβ
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (Ordinal.bddAbove_range _)).1 hβ
    exact ⟨n, lt_of_lt_of_le hn (below n)⟩
  · intro n
    exact lt_of_le_of_lt (restrictedRankLe S wfNative wfFull (t n))
      (upper S wfFull (t n).val indexType (t n).property.1.1 (t n).property.1.2.1)
  · intro q τ hp ho
    exact ne_of_lt (upper S wfFull q τ hp ho)

theorem conditionalHeightEffective : ConditionalHeightEffective.{u} := by
  intro I _ D BH calibration tower endpoint upper
  exact ⟨conditionalHeight I D BH calibration tower endpoint upper,
    effectiveFamily D BH calibration tower endpoint upper⟩

#print axioms conditionalHeightEffective

end LogicLineages.PersistentMarking.ConditionalHeightEffectiveProof
