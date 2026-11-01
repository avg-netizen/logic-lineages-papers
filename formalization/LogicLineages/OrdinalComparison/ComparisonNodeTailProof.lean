module
public import LogicLineages.OrdinalComparison.ComparisonNodeTargets
public import LogicLineages.OrdinalComparison.ComparisonNodeProgramProof
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode

attribute [local irreducible] encodedCollectedNormalize encodedPositiveZeroBound encodedCollectedZeroBound

theorem table_tail_positive (table : ComparisonNodeTable) : 1≤encodedComparisonTableTail table := by
  induction table with
  | nil => exact le_rfl
  | cons a table ih => exact ih.trans (Nat.le_max_right _ _)

theorem table_member_tail (table : ComparisonNodeTable) (q : ComparisonQuery) (result : ComparisonNodeResult)
    (h : (q,result)∈table) : result.2≤encodedComparisonTableTail table := by
  induction table with
  | nil => cases h
  | cons a table ih =>
    rcases List.mem_cons.mp h with heq | hm
    · cases heq
      exact Nat.le_max_left _ _
    · exact (ih hm).trans (Nat.le_max_right _ _)

theorem source_zero_bound (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F) :
    encodedPositiveZeroBound (positiveExprEncode E) (positiveExprEncode F)=
      collectedFiniteZeroBound [collectedPositiveNormalize E,collectedPositiveNormalize F] := by
  unfold encodedPositiveZeroBound
  rw [encodedCollectedNormalizeCorrect E hE,encodedCollectedNormalizeCorrect F hF]
  have h := encodedCollectedZeroBoundCorrect [collectedPositiveNormalize E,collectedPositiveNormalize F]
  simpa only [List.map_cons,List.map_nil] using h

theorem source_tail (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (c b d e : Nat) (tags rest : CollectedPositiveTags)
    (hNE : collectedPositiveNormalize E=.mk c b tags) (hNF : collectedPositiveNormalize F=.mk d e rest) :
    encodedPositiveNodeLocalTail (positiveExprEncode E) (positiveExprEncode F)=
      max (collectedFiniteZeroBound [collectedPositiveNormalize E,collectedPositiveNormalize F]) (c+d+1) := by
  unfold encodedPositiveNodeLocalTail
  rw [source_zero_bound E F hE hF,encodedCollectedNormalizeCorrect E hE,encodedCollectedNormalizeCorrect F hF,
    hNE,hNF]
  simp only [collectedPositiveEncode,Nat.unpair_pair]

theorem sign_of_int_sign (a b c d : Nat)
    (h : Int.sign ((a : Int)-(b : Int))=Int.sign ((c : Int)-(d : Int))) :
    comparisonNaturalSign a b=comparisonNaturalSign c d := by
  have hA : Int.sign ((a : Int)-(b : Int)) = -1 ↔ a<b := by
    rw [Int.sign_eq_neg_one_iff_neg]
    omega
  have hB : Int.sign ((c : Int)-(d : Int)) = -1 ↔ c<d := by
    rw [Int.sign_eq_neg_one_iff_neg]
    omega
  have hA' : Int.sign ((a : Int)-(b : Int)) = 1 ↔ b<a := by
    rw [Int.sign_eq_one_iff_pos]
    omega
  have hB' : Int.sign ((c : Int)-(d : Int)) = 1 ↔ d<c := by
    rw [Int.sign_eq_one_iff_pos]
    omega
  have hl : a<b ↔ c<d := by rw [←hA,←hB,h]
  have hr : b<a ↔ d<c := by rw [←hA',←hB',h]
  unfold comparisonNaturalSign
  simp only [hl,hr]

theorem weak_order_stable (E F : OneVariableComparisonExpr) (result : ComparisonNodeResult)
    (h : comparisonEventualSignData E F result) (x y : Nat) (hx : result.2≤x) (hy : result.2≤y) :
    (actualOneVariableComparisonValue E x≤actualOneVariableComparisonValue F x ↔
      actualOneVariableComparisonValue E y≤actualOneVariableComparisonValue F y) := by
  have h0x := (h.2.2 x hx).2.2.1
  have h1x := (h.2.2 x hx).2.2.2.1
  have h0y := (h.2.2 y hy).2.2.1
  have h1y := (h.2.2 y hy).2.2.2.1
  omega

theorem affine_int_sign_stable (a b c d x y : Nat) (hx : a+c+1≤x) (hy : a+c+1≤y) :
    Int.sign (((a+b*x : Nat) : Int)-((c+d*x : Nat) : Int))=
      Int.sign (((a+b*y : Nat) : Int)-((c+d*y : Nat) : Int)) := by
  by_cases hbd : b<d
  · have hs : ∀ z : Nat,a+c+1≤z → a+b*z<c+d*z := by
      intro z hz
      have hm := Nat.mul_le_mul_right z (Nat.succ_le_of_lt hbd)
      rw [Nat.succ_mul] at hm
      omega
    rw [Int.sign_eq_neg_one_of_neg (by have h := hs x hx; omega),
      Int.sign_eq_neg_one_of_neg (by have h := hs y hy; omega)]
  · by_cases hdb : d<b
    · have hs : ∀ z : Nat,a+c+1≤z → c+d*z<a+b*z := by
        intro z hz
        have hm := Nat.mul_le_mul_right z (Nat.succ_le_of_lt hdb)
        rw [Nat.succ_mul] at hm
        omega
      rw [Int.sign_eq_one_of_pos (by have h := hs x hx; omega),
        Int.sign_eq_one_of_pos (by have h := hs y hy; omega)]
    · have heq : b=d := by omega
      subst d
      apply congrArg Int.sign
      omega

end LogicLineages.OrdinalComparison.ComparisonNode
