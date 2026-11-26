module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSequenceProof
public import LogicLineages.NativeModule.PersistentMarking.NativeRankUnconditionalChecks
public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityProof

@[expose] public section

/-! `thm:height`, following the printed proof: "The realizers (R) and Lemma tower-cofinality give
the lower bound for the restriction to closed native terms. Its ranks are bounded by the ranks in
the full ordering. Theorem upper bounds each individual full rank below BH. Taking the supremum
of ranks plus one gives equality." -/

namespace LogicLineages.PersistentMarking.ConditionalHeightProof
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets NativeRankTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets NativeTowerSequenceTargets
open ConditionalTowerCofinality ExternalOrdinalInterfaceTargets ConditionalHeightTargets

universe u

/-- "Its ranks are bounded by the ranks in the full ordering" (#1448). -/
theorem restrictedRankLe (S : Signature) (wfNative : WellFounded (@NativeBelow S indexType))
    (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t))
    (t : ClosedNativeTerm S indexType) :
    nativeRank (wfNative.apply t) ≤ confinedRank (wfFull.apply t.val) := by
  obtain ⟨_, _, h⟩ := NativeRankUnconditionalChecks.exact_ActualClosedNativeRanks S indexType
  exact (h t).2.1

/-- The restriction's height is at most the full height (closed native terms are ordinary). -/
theorem nativeHeightLe (S : Signature) (wfNative : WellFounded (@NativeBelow S indexType))
    (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t)) :
    nativeHeight S wfNative ≤ descendingHeight S wfFull := by
  refine Ordinal.iSup_le (fun t => ?_)
  let q : OrdinaryTerm S := ⟨t.val, indexType, t.property.1.1, t.property.1.2.1⟩
  exact (Order.succ_le_succ (restrictedRankLe S wfNative wfFull t)).trans
    (Ordinal.le_iSup (fun q : OrdinaryTerm S => Order.succ (confinedRank (wfFull.apply q.val))) q)

/-- "Theorem upper bounds each individual full rank below BH"; supremum of rank + 1. -/
theorem heightLeOfUpper (BH : Ordinal.{0}) (upper : UpperBound BH) (S : Signature)
    (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t)) :
    descendingHeight S wfFull ≤ BH := by
  refine Ordinal.iSup_le (fun q => ?_)
  obtain ⟨τ, hp, ho⟩ := q.property
  exact Order.succ_le_of_lt (upper S wfFull q.val τ hp ho)

/-- (R): each closed native `t_n` has rank at least `ψ_B(a_n)`, from #1462 and E1. -/
theorem towerRanks {I : Type u} [LinearOrder I] (D : CollapseData I Ordinal.{0})
    (calibration : Calibration D) (S : Signature) (wfNative : WellFounded (@NativeBelow S indexType)) :
    ∀ n, ∃ t : ClosedNativeTerm S indexType, t.val = sequenceTerm n ∧
      D.psi (D.a n) ≤ nativeRank (wfNative.apply t) := by
  obtain ⟨Z, s, add, mul, w, one, pow, fix, h1, h2, cal⟩ := calibration
  obtain ⟨_, sequence⟩ := NativeTowerSequenceProof.exact_NativeTowerSequenceRealization S
  intro n
  obtain ⟨t, tv, realizes⟩ := sequence Z s add mul w one pow fix h1 h2 n
  have bound : (sequenceValue fix pow w n).val ≤ nativeRank (wfNative.apply t) := realizes
  rw [cal n] at bound
  exact ⟨t, tv, bound⟩

/-- "The realizers (R) and Lemma tower-cofinality give the lower bound for the restriction." -/
theorem lowerBound {I : Type u} [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0})
    (calibration : Calibration D) (tower : TowerHypotheses D) (endpoint : BHIdentification D BH)
    (S : Signature) (wfNative : WellFounded (@NativeBelow S indexType)) :
    BH ≤ nativeHeight S wfNative := by
  have each : ∀ n, D.psi (D.a n) ≤ nativeHeight S wfNative := by
    intro n
    obtain ⟨t, _, bound⟩ := towerRanks D calibration S wfNative n
    exact bound.trans ((Order.le_succ _).trans
      (Ordinal.le_iSup (fun t : ClosedNativeTerm S indexType => Order.succ (nativeRank (wfNative.apply t))) t))
  have lub : IsLUB (Set.range (fun n => D.psi (D.a n))) (⨆ n, D.psi (D.a n)) :=
    isLUB_ciSup (Ordinal.bddAbove_range _)
  have cofinal := conditionalTowerCofinality I Ordinal.{0} D BH tower endpoint _ lub
  rw [← cofinal.2]
  exact Ordinal.iSup_le each

theorem conditionalHeight : ConditionalHeight.{u} := by
  intro I _ D BH calibration tower endpoint upper S wfFull wfNative
  have low := lowerBound D BH calibration tower endpoint S wfNative
  have mid := nativeHeightLe S wfNative wfFull
  have high := heightLeOfUpper BH upper S wfFull
  exact ⟨le_antisymm high (low.trans mid), le_antisymm (mid.trans high) low⟩

#print axioms conditionalHeight

end LogicLineages.PersistentMarking.ConditionalHeightProof
