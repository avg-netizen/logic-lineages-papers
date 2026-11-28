module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelTwoFunctionProof

@[expose] public section

/-! Function side of a good family `K a : A_1` (`GoodFamily`): the proofs of
`ActualCalibrationLevelTwoFunctionProof` for the orbit `a ↦ G^a H`, read for an arbitrary family with
`B_0 (K a) ≤ K (a+1)` and pointwise suprema at limits. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationUniform
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationStep
open scoped Ordinal

section
variable {Z : CountableOrdinal} {s : CountableOrdinal → CountableOrdinal}
  {add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
  {w one : CountableOrdinal} {pow : CountableOrdinal → CountableOrdinal}
  {fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal}

theorem fam_bdd (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (l x : CountableOrdinal) :
    BddAbove (Set.range (fun e : EarlierStages l => (K (earlierStage l e) x).val)) :=
  bddAbove_orbit .base id (fun e : EarlierStages l => K (earlierStage l e) x)

/-- Monotone in the stage. -/
theorem fam_mono (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K) :
    ∀ a b : CountableOrdinal, b.val ≤ a.val → ∀ x : CountableOrdinal,
      (K b x).val ≤ (K a x).val := by
  refine countable_induction _ ?_ ?_ ?_
  · intro a h0 b hb x
    have hba : b = a := Subtype.ext (le_antisymm hb (by rw [h0]; exact ozl _))
    rw [hba]
  · intro a' a ha ih b hb x
    rcases hb.lt_or_eq with hlt | heq
    · have hb' : b.val ≤ a'.val := by
        rw [ha] at hlt
        exact Order.lt_add_one_iff.1 hlt
      exact (ih b hb' x).trans
        (((b0_monoInfl h1 h2 (K a') (hK.1 a').1).2 x).trans (hK.2.1 a' a ha x))
    · have hba : b = a := Subtype.ext heq
      rw [hba]
  · intro l hl _ b hb x
    rcases hb.lt_or_eq with hlt | heq
    · rw [hK.2.2 l hl x]
      have e : earlierStage l ⟨b.val, hlt⟩ = b := Subtype.ext rfl
      have h := le_ciSup (fam_bdd K l x) ⟨b.val, hlt⟩
      rw [e] at h
      exact h
    · have hbl : b = l := Subtype.ext heq
      rw [hbl]

theorem fam_strict (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (a a' : CountableOrdinal) (ha : a'.val = a.val + 1) (x : CountableOrdinal) :
    (K a x).val < (K a' x).val :=
  lt_of_lt_of_le ((good_b0 h1 h2 (K a) (hK.1 a)).2 x) (hK.2.1 a a' ha x)

/-- Strict in the stage. -/
theorem fam_lt (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (a b : CountableOrdinal) (hab : a.val < b.val) (x : CountableOrdinal) :
    (K a x).val < (K b x).val := by
  obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
  exact lt_of_lt_of_le (fam_strict h1 h2 K hK a a1 ha1 x)
    (fam_mono h1 h2 K hK b a1 (by rw [ha1]; exact Order.add_one_le_of_lt hab) x)

theorem fam_diag_id_le (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K) :
    ∀ a : CountableOrdinal, a.val ≤ (K a zeroValue).val := by
  refine countable_strong_induction _ (fun a ih => ?_)
  by_contra hlt
  rw [not_le] at hlt
  have p := ih (K a zeroValue) hlt
  have q := fam_lt h1 h2 K hK (K a zeroValue) a hlt zeroValue
  exact absurd p (not_le.2 q)

theorem fam_lt_limit (K : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (hK : GoodFamily fix pow w K) (l : CountableOrdinal) (hl : Order.IsSuccLimit l.val)
    (x : CountableOrdinal) (y : Ordinal.{0}) (h : y < (K l x).val) :
    ∃ b : CountableOrdinal, b.val < l.val ∧ y < (K b x).val := by
  haveI : Nonempty (EarlierStages l) := ⟨⟨0, hl.bot_lt⟩⟩
  rw [hK.2.2 l hl x] at h
  obtain ⟨e, he⟩ := (lt_ciSup_iff (fam_bdd K l x)).1 h
  exact ⟨earlierStage l e, e.property, he⟩

theorem fam_limit_le (K : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (hK : GoodFamily fix pow w K) (l : CountableOrdinal) (hl : Order.IsSuccLimit l.val)
    (x : CountableOrdinal) (b : Ordinal.{0})
    (Hb : ∀ a : CountableOrdinal, a.val < l.val → (K a x).val ≤ b) : (K l x).val ≤ b := by
  rw [hK.2.2 l hl x]
  exact ciSup_le' (fun e => Hb (earlierStage l e) e.property)

theorem fam_fix_limit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (κ : CountableOrdinal) (hκ : K κ zeroValue = κ) (hpos : 0 < κ.val) :
    Order.IsSuccLimit κ.val := by
  rcases countable_cases κ with h0 | ⟨c, hc⟩ | hl
  · exact absurd hpos (by rw [h0]; exact lt_irrefl _)
  · exfalso
    have gK := hK.1 c
    obtain ⟨hfix, hpos0, -⟩ := b0_spec h1 h2 (K c) gK.1 zeroValue
    have blim := gfix_limit h1 h2 (K c) gK.1 gK.2.1 (towerValue fix 0 (K c) zeroValue) hfix hpos0
    have a1 : c.val < (towerValue fix 0 (K c) zeroValue).val :=
      lt_of_le_of_lt (fam_diag_id_le h1 h2 K hK c) ((good_b0 h1 h2 (K c) gK).2 zeroValue)
    have a2 := blim.add_one_lt a1
    have a3 := hK.2.1 c κ hc zeroValue
    rw [hκ] at a3
    rw [← hc] at a2
    exact absurd a3 (not_le.2 a2)
  · exact hl

theorem fam_fix_closed (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (κ : CountableOrdinal) (hκ : K κ zeroValue = κ) (hpos : 0 < κ.val) (a x : CountableOrdinal)
    (ha : a.val < κ.val) (hx : x.val < κ.val) : (K a x).val < κ.val := by
  have hl := fam_fix_limit h1 h2 K hK κ hκ hpos
  have hx' : x.val < (K κ zeroValue).val := lt_of_lt_of_eq hx (congrArg Subtype.val hκ).symm
  obtain ⟨b, hb, hxb⟩ := fam_lt_limit K hK κ hl zeroValue x.val hx'
  have hmax : max a.val b.val < κ.val := max_lt ha hb
  obtain ⟨m, hm⟩ := countable_mk (max a.val b.val) (hmax.trans (countable_val_lt κ))
  obtain ⟨m1, hm1⟩ := countable_mk (m.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt m))
  have hm1κ : m1.val ≤ κ.val := by
    rw [hm1, hm]
    exact (hl.add_one_lt hmax).le
  have gm := hK.1 m
  have s1 : (K a x).val ≤ (K m x).val :=
    fam_mono h1 h2 K hK m a (by rw [hm]; exact le_max_left _ _) x
  have s2 : (K b zeroValue).val ≤ (K m zeroValue).val :=
    fam_mono h1 h2 K hK m b (by rw [hm]; exact le_max_right _ _) zeroValue
  have s3 : (K m x).val ≤ (K m (K m zeroValue)).val :=
    gm.1.1 x (K m zeroValue) (hxb.le.trans s2)
  have s4 := b0_zero_gt h1 h2 (K m) gm
  have s5 := hK.2.1 m m1 hm1 zeroValue
  have s6 : (K m1 zeroValue).val ≤ (K κ zeroValue).val :=
    fam_mono h1 h2 K hK κ m1 hm1κ zeroValue
  rw [hκ] at s6
  exact lt_of_le_of_lt (s1.trans s3) (lt_of_lt_of_le s4 (s5.trans s6))

theorem fam_fix_crit (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (κ : CountableOrdinal) (hκ : K κ zeroValue = κ)
    (hΓκ : (baseValue fix pow w).val < κ.val) :
    Critical (veblenValue fix pow) (baseValue fix pow w) κ.val := by
  have hpos : 0 < κ.val := lt_of_le_of_lt (ozl _) hΓκ
  have hl := fam_fix_limit h1 h2 K hK κ hκ hpos
  refine critLim h1 h2 κ hpos (fun y hy => ?_)
  have hy' : y.val < (K κ zeroValue).val := lt_of_lt_of_eq hy (congrArg Subtype.val hκ).symm
  obtain ⟨b, hb, hyb⟩ := fam_lt_limit K hK κ hl zeroValue y.val hy'
  have gb := hK.1 b
  refine ⟨K b (baseValue fix pow w), gb.2.2 (baseValue fix pow w) crit_base, ?_, ?_⟩
  · exact lt_of_lt_of_le hyb (gb.1.1 zeroValue (baseValue fix pow w) (ozl _))
  · exact (fam_fix_closed h1 h2 K hK κ hκ hpos b (baseValue fix pow w) hb hΓκ).le

/-- `fix (a ↦ K a 0) x` is the least fixed point of `a ↦ K a 0` above `x`. -/
theorem fam_spec (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (x : CountableOrdinal) :
    K (fix (fun a => K a zeroValue) x) zeroValue = fix (fun a => K a zeroValue) x ∧
    x.val < (fix (fun a => K a zeroValue) x).val ∧
    ∀ θ : CountableOrdinal, x.val < θ.val → K θ zeroValue = θ →
      (fix (fun a => K a zeroValue) x).val ≤ θ.val :=
  fixLeastAbove Z s add mul w one pow fix h1 h2 (fun a => K a zeroValue)
    (fun x y hxy => fam_mono h1 h2 K hK y x hxy zeroValue)
    (fun x => fam_diag_id_le h1 h2 K hK x)
    (fun l hl => hK.2.2 l hl zeroValue) x

/-- `B_0 (K a) x < fix (a ↦ K a 0) x` for `a` below the value. -/
theorem fam_b0_lt (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K)
    (a x : CountableOrdinal) (ha : a.val < (fix (fun a => K a zeroValue) x).val) :
    (towerValue fix 0 (K a) x).val < (fix (fun a => K a zeroValue) x).val := by
  obtain ⟨hfix, hx, -⟩ := fam_spec h1 h2 K hK x
  have hpos : 0 < (fix (fun a => K a zeroValue) x).val := lt_of_le_of_lt (ozl _) hx
  have hl := fam_fix_limit h1 h2 K hK _ hfix hpos
  obtain ⟨a1, ha1⟩ := countable_mk (a.val + 1)
    ((isSuccLimit_omega 1).add_one_lt (countable_val_lt a))
  have ha1κ : a1.val < (fix (fun a => K a zeroValue) x).val := by
    rw [ha1]
    exact hl.add_one_lt ha
  exact lt_of_le_of_lt (hK.2.1 a a1 ha1 x)
    (fam_fix_closed h1 h2 K hK _ hfix hpos a1 x ha1κ hx)

theorem fam_fix_good (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) (hK : GoodFamily fix pow w K) :
    GoodFn fix pow w (fix (fun a => K a zeroValue)) := by
  have mi : MonoInfl (fix (fun a => K a zeroValue)) :=
    fix_monoInfl h1 h2 (fun a => K a zeroValue)
      (fun x y hxy => fam_mono h1 h2 K hK y x hxy zeroValue)
  refine ⟨mi, fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨-, hy, -⟩ := fam_spec h1 h2 K hK y
    have h0 : zeroValue.val < (fix (fun a => K a zeroValue) y).val :=
      lt_of_le_of_lt (ozl _) hy
    exact (((hK.1 zeroValue).2.1 y).trans
      ((b0_monoInfl h1 h2 (K zeroValue) (hK.1 zeroValue).1).2 y)).trans
      (fam_b0_lt h1 h2 K hK zeroValue y h0).le
  · obtain ⟨hfix, hxκ, -⟩ := fam_spec h1 h2 K hK x
    exact fam_fix_crit h1 h2 K hK _ hfix (lt_of_le_of_lt (crit_ge_base h1 h2 hx) hxκ)

end

theorem familyDiagonal : FamilyDiagonal := by
  intro Z s add mul w one pow fix h1 h2 K hK
  refine ⟨fun a b x hab => fam_mono h1 h2 K hK b a hab x,
    fun a a' x ha => fam_strict h1 h2 K hK a a' ha x,
    fam_diag_id_le h1 h2 K hK,
    fun κ hκ hpos => ⟨fam_fix_limit h1 h2 K hK κ hκ hpos,
      fun a x ha hx => fam_fix_closed h1 h2 K hK κ hκ hpos a x ha hx⟩,
    fun κ hκ hΓ => fam_fix_crit h1 h2 K hK κ hκ hΓ,
    fun x => fam_spec h1 h2 K hK x,
    fam_fix_good h1 h2 K hK,
    fun a x ha => fam_b0_lt h1 h2 K hK a x ha⟩

#print axioms familyDiagonal

end LogicLineages.PersistentMarking.ActualCalibrationUniform
