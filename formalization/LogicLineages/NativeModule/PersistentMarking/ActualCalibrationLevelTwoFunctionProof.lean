module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelTwoTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepOrbitProof

@[expose] public section

/-! Function side at type `A_2`: orbits `a ↦ G^a H` of a good operator `G`, the fixed points of
their zero-diagonal `a ↦ (G^a H) 0` (limits, closed under the family, critical above `Γ_0`),
`B_1 G H x` as the least such fixed point above `x`, `B_1` preserves good operators, and the
operators `B_1^e B_0`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

/-- `B_0 K x` is the least fixed point of `a ↦ K^a(0)` above `x`. -/
theorem b0_spec (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal) (hK : MonoInfl K) (x : CountableOrdinal) :
    orbit .base K zeroValue (towerValue fix 0 K x) = towerValue fix 0 K x ∧
    x.val < (towerValue fix 0 K x).val ∧
    ∀ θ : CountableOrdinal, x.val < θ.val → orbit .base K zeroValue θ = θ →
      (towerValue fix 0 K x).val ≤ θ.val := by
  rw [b0_eq]
  exact fixLeastAbove Z s add mul w one pow fix h1 h2 (fun α => orbit .base K zeroValue α)
    (fun x y hxy => orbit_mono K zeroValue hK.2 hxy)
    (fun x => orbit_id_le K zeroValue hK.2 x)
    (fun l hl => orbit_limit_eq K zeroValue l hl) x

/-- For good `K`: `K (K 0) < B_0 K 0`. -/
theorem b0_zero_gt (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal) (hK : GoodFn fix pow w K) :
    (K (K zeroValue)).val < (towerValue fix 0 K zeroValue).val := by
  obtain ⟨hfix, hpos, -⟩ := b0_spec h1 h2 K hK.1 zeroValue
  exact gfix_closed h1 h2 K hK.1 hK.2.1 (towerValue fix 0 K zeroValue) hfix hpos (K zeroValue)
    ((good_b0 h1 h2 K hK).2 zeroValue)

/-! Orbits of a good operator. -/

theorem op_orbit_good (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) :
    ∀ a : CountableOrdinal, GoodFn fix pow w (orbit (tier 1) G H a) ∧
      ∀ b : CountableOrdinal, b.val ≤ a.val → ∀ x : CountableOrdinal,
        (orbit (tier 1) G H b x).val ≤ (orbit (tier 1) G H a x).val := by
  have eqs := orbitEquations (tier 1) G H
  refine countable_induction _ ?_ ?_ ?_
  · intro a h0
    rw [eqs.1 a h0]
    refine ⟨hH, fun b hb x => ?_⟩
    have hba : b = a := Subtype.ext (le_antisymm hb (by rw [h0]; exact ozl _))
    rw [hba, eqs.1 a h0]
  · intro a' a ha ih
    rw [eqs.2.1 a' a ha]
    obtain ⟨gK, dom⟩ := hG (orbit (tier 1) G H a') ih.1
    refine ⟨gK, fun b hb x => ?_⟩
    rcases hb.lt_or_eq with hlt | heq
    · have hb' : b.val ≤ a'.val := by
        rw [ha] at hlt
        exact Order.lt_add_one_iff.1 hlt
      exact (ih.2 b hb' x).trans
        (((b0_monoInfl h1 h2 (orbit (tier 1) G H a') ih.1.1).2 x).trans (dom x))
    · have hba : b = a := Subtype.ext heq
      rw [hba, eqs.2.1 a' a ha]
  · intro l hl ih
    have sup : ∀ x : CountableOrdinal, (orbit (tier 1) G H l x).val =
        ⨆ e : EarlierStages l, (orbit (tier 1) G H (earlierStage l e) x).val :=
      fun x => eqs.2.2 l hl x
    have bdd : ∀ x : CountableOrdinal, BddAbove (Set.range (fun e : EarlierStages l =>
        (orbit (tier 1) G H (earlierStage l e) x).val)) := fun x =>
      bddAbove_orbit .base id (fun e : EarlierStages l => orbit (tier 1) G H (earlierStage l e) x)
    let e0 : EarlierStages l := ⟨0, hl.bot_lt⟩
    haveI : Nonempty (EarlierStages l) := ⟨e0⟩
    have stage : ∀ b : CountableOrdinal, b.val ≤ l.val → ∀ x : CountableOrdinal,
        (orbit (tier 1) G H b x).val ≤ (orbit (tier 1) G H l x).val := by
      intro b hb x
      rcases hb.lt_or_eq with hlt | heq
      · rw [sup x]
        have e : earlierStage l ⟨b.val, hlt⟩ = b := Subtype.ext rfl
        have h := le_ciSup (bdd x) ⟨b.val, hlt⟩
        rw [e] at h
        exact h
      · have hbl : b = l := Subtype.ext heq
        rw [hbl]
    have mono : ∀ x y : CountableOrdinal, x.val ≤ y.val →
        (orbit (tier 1) G H l x).val ≤ (orbit (tier 1) G H l y).val := by
      intro x y hxy
      rw [sup x, sup y]
      exact ciSup_le' (fun e =>
        ((ih (earlierStage l e) e.property).1.1.1 x y hxy).trans (le_ciSup (bdd y) e))
    have infl : ∀ x : CountableOrdinal, x.val < (orbit (tier 1) G H l x).val := by
      intro x
      rw [sup x]
      exact lt_of_lt_of_le ((ih (earlierStage l e0) e0.property).1.1.2 x) (le_ciSup (bdd x) e0)
    have geN : ∀ y : CountableOrdinal,
        (veblenValue fix pow y).val ≤ (orbit (tier 1) G H l y).val := by
      intro y
      have h := stage zeroValue (ozl _) y
      rw [eqs.1 zeroValue rfl] at h
      exact (hH.2.1 y).trans h
    have crit : ∀ x : CountableOrdinal,
        Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
        Critical (veblenValue fix pow) (baseValue fix pow w) (orbit (tier 1) G H l x).val := by
      intro x hx
      refine critLim h1 h2 (orbit (tier 1) G H l x) (lt_of_le_of_lt (ozl _) (infl x))
        (fun y hy => ?_)
      have hy' := hy
      rw [sup x] at hy'
      obtain ⟨e, he⟩ := (lt_ciSup_iff (bdd x)).1 hy'
      exact ⟨orbit (tier 1) G H (earlierStage l e) x,
        (ih (earlierStage l e) e.property).1.2.2 x hx, he,
        stage (earlierStage l e) e.property.le x⟩
    exact ⟨⟨⟨mono, infl⟩, geN, crit⟩, stage⟩

theorem op_orbit_strict (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) (a a' : CountableOrdinal) (ha : a'.val = a.val + 1)
    (x : CountableOrdinal) :
    (orbit (tier 1) G H a x).val < (orbit (tier 1) G H a' x).val := by
  have gK := (op_orbit_good h1 h2 G hG H hH a).1
  rw [(orbitEquations (tier 1) G H).2.1 a a' ha]
  exact lt_of_lt_of_le ((good_b0 h1 h2 (orbit (tier 1) G H a) gK).2 x)
    ((hG (orbit (tier 1) G H a) gK).2 x)

theorem op_diag_strict (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) (a b : CountableOrdinal) (hab : a.val < b.val) :
    (orbit (tier 1) G H a zeroValue).val < (orbit (tier 1) G H b zeroValue).val := by
  obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
  exact lt_of_lt_of_le (op_orbit_strict h1 h2 G hG H hH a a1 ha1 zeroValue)
    ((op_orbit_good h1 h2 G hG H hH b).2 a1 (by rw [ha1]; exact Order.add_one_le_of_lt hab)
      zeroValue)

theorem op_diag_id_le (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) :
    ∀ a : CountableOrdinal, a.val ≤ (orbit (tier 1) G H a zeroValue).val := by
  refine countable_strong_induction _ (fun a ih => ?_)
  by_contra hlt
  rw [not_le] at hlt
  have p := ih (orbit (tier 1) G H a zeroValue) hlt
  have q := op_diag_strict h1 h2 G hG H hH (orbit (tier 1) G H a zeroValue) a hlt
  exact absurd p (not_le.2 q)

theorem lt_op_diag_limit
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (H : CountableOrdinal → CountableOrdinal) (l : CountableOrdinal)
    (hl : Order.IsSuccLimit l.val) (y : Ordinal.{0})
    (h : y < (orbit (tier 1) G H l zeroValue).val) :
    ∃ b : CountableOrdinal, b.val < l.val ∧ y < (orbit (tier 1) G H b zeroValue).val := by
  haveI : Nonempty (EarlierStages l) := ⟨⟨0, hl.bot_lt⟩⟩
  have sup : (orbit (tier 1) G H l zeroValue).val =
      ⨆ e : EarlierStages l, (orbit (tier 1) G H (earlierStage l e) zeroValue).val :=
    (orbitEquations (tier 1) G H).2.2 l hl zeroValue
  rw [sup] at h
  obtain ⟨e, he⟩ := (lt_ciSup_iff (bddAbove_orbit .base id
    (fun e : EarlierStages l => orbit (tier 1) G H (earlierStage l e) zeroValue))).1 h
  exact ⟨earlierStage l e, e.property, he⟩

theorem op_diag_limit_le
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (H : CountableOrdinal → CountableOrdinal) (l : CountableOrdinal)
    (hl : Order.IsSuccLimit l.val) (b : Ordinal.{0})
    (Hb : ∀ a : CountableOrdinal, a.val < l.val → (orbit (tier 1) G H a zeroValue).val ≤ b) :
    (orbit (tier 1) G H l zeroValue).val ≤ b := by
  have sup : (orbit (tier 1) G H l zeroValue).val =
      ⨆ e : EarlierStages l, (orbit (tier 1) G H (earlierStage l e) zeroValue).val :=
    (orbitEquations (tier 1) G H).2.2 l hl zeroValue
  rw [sup]
  exact ciSup_le' (fun e => Hb (earlierStage l e) e.property)

/-! Fixed points of the zero-diagonal `a ↦ (G^a H) 0`. -/

theorem op_fix_limit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) (κ : CountableOrdinal)
    (hκ : orbit (tier 1) G H κ zeroValue = κ) (hpos : 0 < κ.val) : Order.IsSuccLimit κ.val := by
  rcases countable_cases κ with h0 | ⟨c, hc⟩ | hl
  · exact absurd hpos (by rw [h0]; exact lt_irrefl _)
  · exfalso
    have gK := (op_orbit_good h1 h2 G hG H hH c).1
    obtain ⟨hfix, hpos0, -⟩ := b0_spec h1 h2 (orbit (tier 1) G H c) gK.1 zeroValue
    have blim := gfix_limit h1 h2 (orbit (tier 1) G H c) gK.1 gK.2.1
      (towerValue fix 0 (orbit (tier 1) G H c) zeroValue) hfix hpos0
    have a1 : c.val < (towerValue fix 0 (orbit (tier 1) G H c) zeroValue).val :=
      lt_of_le_of_lt (op_diag_id_le h1 h2 G hG H hH c)
        ((good_b0 h1 h2 (orbit (tier 1) G H c) gK).2 zeroValue)
    have a2 := blim.add_one_lt a1
    have a3 := (hG (orbit (tier 1) G H c) gK).2 zeroValue
    rw [← (orbitEquations (tier 1) G H).2.1 c κ hc, hκ] at a3
    rw [← hc] at a2
    exact absurd a3 (not_le.2 a2)
  · exact hl

theorem op_fix_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) (κ : CountableOrdinal)
    (hκ : orbit (tier 1) G H κ zeroValue = κ) (hpos : 0 < κ.val) (a x : CountableOrdinal)
    (ha : a.val < κ.val) (hx : x.val < κ.val) :
    (orbit (tier 1) G H a x).val < κ.val := by
  have hl := op_fix_limit h1 h2 G hG H hH κ hκ hpos
  have hx' : x.val < (orbit (tier 1) G H κ zeroValue).val :=
    lt_of_lt_of_eq hx (congrArg Subtype.val hκ).symm
  obtain ⟨b, hb, hxb⟩ := lt_op_diag_limit G H κ hl x.val hx'
  have hmax : max a.val b.val < κ.val := max_lt ha hb
  obtain ⟨m, hm⟩ := countable_mk (max a.val b.val) (hmax.trans (countable_val_lt κ))
  obtain ⟨m1, hm1⟩ := countable_mk (m.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt m))
  have hm1κ : m1.val ≤ κ.val := by
    rw [hm1, hm]
    exact (hl.add_one_lt hmax).le
  have gm := op_orbit_good h1 h2 G hG H hH m
  have s1 : (orbit (tier 1) G H a x).val ≤ (orbit (tier 1) G H m x).val :=
    gm.2 a (by rw [hm]; exact le_max_left _ _) x
  have s2 : (orbit (tier 1) G H b zeroValue).val ≤ (orbit (tier 1) G H m zeroValue).val :=
    gm.2 b (by rw [hm]; exact le_max_right _ _) zeroValue
  have s3 : (orbit (tier 1) G H m x).val ≤
      (orbit (tier 1) G H m (orbit (tier 1) G H m zeroValue)).val :=
    gm.1.1.1 x (orbit (tier 1) G H m zeroValue) (hxb.le.trans s2)
  have s4 := b0_zero_gt h1 h2 (orbit (tier 1) G H m) gm.1
  have s5 := (hG (orbit (tier 1) G H m) gm.1).2 zeroValue
  rw [← (orbitEquations (tier 1) G H).2.1 m m1 hm1] at s5
  have s6 : (orbit (tier 1) G H m1 zeroValue).val ≤ (orbit (tier 1) G H κ zeroValue).val :=
    (op_orbit_good h1 h2 G hG H hH κ).2 m1 hm1κ zeroValue
  rw [hκ] at s6
  exact lt_of_le_of_lt (s1.trans s3) (lt_of_lt_of_le s4 (s5.trans s6))

theorem op_fix_crit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) (κ : CountableOrdinal)
    (hκ : orbit (tier 1) G H κ zeroValue = κ) (hΓκ : (baseValue fix pow w).val < κ.val) :
    Critical (veblenValue fix pow) (baseValue fix pow w) κ.val := by
  have hpos : 0 < κ.val := lt_of_le_of_lt (ozl _) hΓκ
  have hl := op_fix_limit h1 h2 G hG H hH κ hκ hpos
  refine critLim h1 h2 κ hpos (fun y hy => ?_)
  have hy' : y.val < (orbit (tier 1) G H κ zeroValue).val :=
    lt_of_lt_of_eq hy (congrArg Subtype.val hκ).symm
  obtain ⟨b, hb, hyb⟩ := lt_op_diag_limit G H κ hl y.val hy'
  have gb := (op_orbit_good h1 h2 G hG H hH b).1
  refine ⟨orbit (tier 1) G H b (baseValue fix pow w), gb.2.2 (baseValue fix pow w) crit_base, ?_, ?_⟩
  · exact lt_of_lt_of_le hyb (gb.1.1 zeroValue (baseValue fix pow w) (ozl _))
  · exact (op_fix_closed h1 h2 G hG H hH κ hκ hpos b (baseValue fix pow w) hb hΓκ).le

/-- `B_1 G H x` is the least fixed point of `a ↦ (G^a H) 0` above `x`. -/
theorem b1_spec (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (H : CountableOrdinal → CountableOrdinal)
    (hH : GoodFn fix pow w H) (x : CountableOrdinal) :
    orbit (tier 1) G H (towerValue fix 1 G H x) zeroValue = towerValue fix 1 G H x ∧
    x.val < (towerValue fix 1 G H x).val ∧
    ∀ θ : CountableOrdinal, x.val < θ.val → orbit (tier 1) G H θ zeroValue = θ →
      (towerValue fix 1 G H x).val ≤ θ.val := by
  rw [NativeTowerProof.towerValue_one]
  exact fixLeastAbove Z s add mul w one pow fix h1 h2
    (fun α => orbit (tier 1) G H α zeroValue)
    (fun x y hxy => (op_orbit_good h1 h2 G hG H hH y).2 x hxy zeroValue)
    (fun x => op_diag_id_le h1 h2 G hG H hH x)
    (fun l hl => (orbitEquations (tier 1) G H).2.2 l hl zeroValue) x

/-- `K^a(0) ≤ (G^a K) 0`. -/
theorem korbit_le_diag (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (hG : GoodOp fix pow w G) (K : CountableOrdinal → CountableOrdinal)
    (hK : GoodFn fix pow w K) :
    ∀ a : CountableOrdinal,
      (orbit .base K zeroValue a).val ≤ (orbit (tier 1) G K a zeroValue).val := by
  have eqs := orbitEquations (tier 1) G K
  refine countable_induction _ ?_ ?_ ?_
  · intro a h0
    rw [orbit_zero K zeroValue a h0]
    exact ozl _
  · intro a' a ha ih
    have ga := op_orbit_good h1 h2 G hG K hK a'
    have k0 : ∀ y : CountableOrdinal, (K y).val ≤ (orbit (tier 1) G K a' y).val := by
      intro y
      have h := ga.2 zeroValue (ozl _) y
      rw [eqs.1 zeroValue rfl] at h
      exact h
    have t1 : (K (orbit .base K zeroValue a')).val ≤
        (orbit (tier 1) G K a' (orbit (tier 1) G K a' zeroValue)).val :=
      (hK.1.1 _ _ ih).trans (k0 (orbit (tier 1) G K a' zeroValue))
    have t2 := b0_zero_gt h1 h2 (orbit (tier 1) G K a') ga.1
    have t3 := (hG (orbit (tier 1) G K a') ga.1).2 zeroValue
    rw [← eqs.2.1 a' a ha] at t3
    rw [orbit_succ K zeroValue a' a ha]
    exact t1.trans (t2.le.trans t3)
  · intro l hl ih
    refine orbit_limit_le K zeroValue l hl _ (fun β hβ => ?_)
    exact (ih β hβ).trans ((op_orbit_good h1 h2 G hG K hK l).2 β hβ.le zeroValue)

end

theorem opSuccessor : OpSuccessor := by
  intro Z s add mul w one pow fix h1 h2 G hG
  have strict : ∀ K : CountableOrdinal → CountableOrdinal, GoodFn fix pow w K →
      ∀ x : CountableOrdinal, (G K x).val < (towerValue fix 1 G K x).val := by
    intro K hK x
    obtain ⟨hfix, hx, -⟩ := b1_spec h1 h2 G hG K hK x
    have hpos : 0 < (towerValue fix 1 G K x).val := lt_of_le_of_lt (ozl _) hx
    have hl := op_fix_limit h1 h2 G hG K hK (towerValue fix 1 G K x) hfix hpos
    obtain ⟨o1, ho1⟩ := countable_mk 1 one_lt_index
    have eqs := orbitEquations (tier 1) G K
    have e1 : orbit (tier 1) G K o1 = G K := by
      rw [eqs.2.1 zeroValue o1 (ho1.trans (zero_add (1 : Ordinal.{0})).symm), eqs.1 zeroValue rfl]
    have h := op_fix_closed h1 h2 G hG K hK (towerValue fix 1 G K x) hfix hpos o1 x
      (by rw [ho1]; exact Ordinal.one_lt_of_isSuccLimit hl) hx
    rw [e1] at h
    exact h
  refine ⟨fun K hK => ?_, strict⟩
  have eD : towerValue fix 1 G K = fix (fun α => orbit (tier 1) G K α zeroValue) :=
    NativeTowerProof.towerValue_one fix G K
  have dom : ∀ x : CountableOrdinal,
      (towerValue fix 0 K x).val ≤ (towerValue fix 1 G K x).val := by
    intro x
    obtain ⟨hfix, hx, -⟩ := b1_spec h1 h2 G hG K hK x
    refine (b0_spec h1 h2 K hK.1 x).2.2 (towerValue fix 1 G K x) hx (Subtype.ext ?_)
    refine le_antisymm ?_ (orbit_id_le K zeroValue hK.1.2 (towerValue fix 1 G K x))
    have h := korbit_le_diag h1 h2 G hG K hK (towerValue fix 1 G K x)
    rw [hfix] at h
    exact h
  have mi : MonoInfl (towerValue fix 1 G K) := by
    rw [eD]
    exact fix_monoInfl h1 h2 (fun α => orbit (tier 1) G K α zeroValue)
      (fun x y hxy => (op_orbit_good h1 h2 G hG K hK y).2 x hxy zeroValue)
  refine ⟨⟨mi, fun y => ?_, fun x hx => ?_⟩, dom⟩
  · exact (hK.2.1 y).trans (((b0_monoInfl h1 h2 K hK.1).2 y).trans (dom y))
  · obtain ⟨hfix, hxκ, -⟩ := b1_spec h1 h2 G hG K hK x
    exact op_fix_crit h1 h2 G hG K hK (towerValue fix 1 G K x) hfix
      (lt_of_le_of_lt (crit_ge_base h1 h2 hx) hxκ)

theorem levelTwoGood : LevelTwoGood := by
  intro Z s add mul w one pow fix h1 h2
  have eqs := orbitEquations (tier 2) (towerValue fix 1) (towerValue fix 0)
  have main : ∀ e : CountableOrdinal, GoodOp fix pow w (levelTwo fix e) ∧
      ∀ e0 : CountableOrdinal, e0.val ≤ e.val → ∀ K : CountableOrdinal → CountableOrdinal,
        GoodFn fix pow w K → ∀ x : CountableOrdinal,
          (levelTwo fix e0 K x).val ≤ (levelTwo fix e K x).val := by
    refine countable_induction _ ?_ ?_ ?_
    · intro e h0
      have e0eq : levelTwo fix e = towerValue fix 0 := eqs.1 e h0
      rw [e0eq]
      refine ⟨fun K hK => ⟨(good_b0 h1 h2 K hK).1, fun x => le_rfl⟩, fun e0 he0 K _ x => ?_⟩
      have hee : e0 = e := Subtype.ext (le_antisymm he0 (by rw [h0]; exact ozl _))
      rw [hee, e0eq]
    · intro e' e he ih
      have eeq : levelTwo fix e = towerValue fix 1 (levelTwo fix e') := eqs.2.1 e' e he
      obtain ⟨gop, strict⟩ := opSuccessor Z s add mul w one pow fix h1 h2 (levelTwo fix e') ih.1
      rw [eeq]
      refine ⟨gop, fun e0 he0 K hK x => ?_⟩
      rcases he0.lt_or_eq with hlt | heq
      · have he0' : e0.val ≤ e'.val := by
          rw [he] at hlt
          exact Order.lt_add_one_iff.1 hlt
        exact (ih.2 e0 he0' K hK x).trans (strict K hK x).le
      · have hee : e0 = e := Subtype.ext heq
        rw [hee, eeq]
    · intro l hl ih
      have sup : ∀ (K : CountableOrdinal → CountableOrdinal) (x : CountableOrdinal),
          (levelTwo fix l K x).val =
            ⨆ e : EarlierStages l, (levelTwo fix (earlierStage l e) K x).val :=
        fun K x => eqs.2.2 l hl K x
      have bdd : ∀ (K : CountableOrdinal → CountableOrdinal) (x : CountableOrdinal),
          BddAbove (Set.range (fun e : EarlierStages l =>
            (levelTwo fix (earlierStage l e) K x).val)) := fun K x =>
        bddAbove_orbit .base id (fun e : EarlierStages l => levelTwo fix (earlierStage l e) K x)
      let e0 : EarlierStages l := ⟨0, hl.bot_lt⟩
      haveI : Nonempty (EarlierStages l) := ⟨e0⟩
      have stage : ∀ b : CountableOrdinal, b.val ≤ l.val →
          ∀ K : CountableOrdinal → CountableOrdinal, GoodFn fix pow w K → ∀ x : CountableOrdinal,
            (levelTwo fix b K x).val ≤ (levelTwo fix l K x).val := by
        intro b hb K _ x
        rcases hb.lt_or_eq with hlt | heq
        · rw [sup K x]
          have e : earlierStage l ⟨b.val, hlt⟩ = b := Subtype.ext rfl
          have h := le_ciSup (bdd K x) ⟨b.val, hlt⟩
          rw [e] at h
          exact h
        · have hbl : b = l := Subtype.ext heq
          rw [hbl]
      refine ⟨fun K hK => ?_, stage⟩
      have mono : ∀ x y : CountableOrdinal, x.val ≤ y.val →
          (levelTwo fix l K x).val ≤ (levelTwo fix l K y).val := by
        intro x y hxy
        rw [sup K x, sup K y]
        exact ciSup_le' (fun e =>
          (((ih (earlierStage l e) e.property).1 K hK).1.1.1 x y hxy).trans (le_ciSup (bdd K y) e))
      have dom : ∀ x : CountableOrdinal,
          (towerValue fix 0 K x).val ≤ (levelTwo fix l K x).val := by
        intro x
        exact (((ih (earlierStage l e0) e0.property).1 K hK).2 x).trans
          (stage (earlierStage l e0) e0.property.le K hK x)
      have infl : ∀ x : CountableOrdinal, x.val < (levelTwo fix l K x).val :=
        fun x => lt_of_lt_of_le ((good_b0 h1 h2 K hK).1.1.2 x) (dom x)
      have geN : ∀ y : CountableOrdinal,
          (veblenValue fix pow y).val ≤ (levelTwo fix l K y).val :=
        fun y => ((good_b0 h1 h2 K hK).1.2.1 y).trans (dom y)
      have crit : ∀ x : CountableOrdinal,
          Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
          Critical (veblenValue fix pow) (baseValue fix pow w) (levelTwo fix l K x).val := by
        intro x hx
        refine critLim h1 h2 (levelTwo fix l K x) (lt_of_le_of_lt (ozl _) (infl x))
          (fun y hy => ?_)
        have hy' := hy
        rw [sup K x] at hy'
        obtain ⟨e, he⟩ := (lt_ciSup_iff (bdd K x)).1 hy'
        exact ⟨levelTwo fix (earlierStage l e) K x,
          ((ih (earlierStage l e) e.property).1 K hK).1.2.2 x hx, he,
          stage (earlierStage l e) e.property.le K hK x⟩
      exact ⟨⟨⟨mono, infl⟩, geN, crit⟩, dom⟩
  refine ⟨fun e => (main e).1, fun e e' K hK h x => (main e').2 e h K hK x,
    fun e e' K hK he x => ?_⟩
  have eeq : levelTwo fix e' = towerValue fix 1 (levelTwo fix e) := eqs.2.1 e e' he
  rw [eeq]
  exact (opSuccessor Z s add mul w one pow fix h1 h2 (levelTwo fix e) (main e).1).2 K hK x

#print axioms opSuccessor
#print axioms levelTwoGood

end LogicLineages.PersistentMarking.ActualCalibrationStep
