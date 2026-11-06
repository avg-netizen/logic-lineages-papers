module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchTargets
import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchOrderProof
open PolynomialGraphCompletion CanonicalGuardSelector

theorem lexOrder_eq_zero (a b : Nat) :
    lexOrder a b = 0 ↔ a = 0 ∨ a = 1 ∧ b = 0 := by
  by_cases h : a = 1 <;> simp [lexOrder, liftTie, h]

theorem lexOrder_eq_one (a b : Nat) :
    lexOrder a b = 1 ↔ a = 1 ∧ b = 1 := by
  by_cases h : a = 1 <;> simp [lexOrder, liftTie, h]

theorem liftTie_orderNat_eq_zero (tie u v : Nat) :
    liftTie tie (orderNat u v) = 0 ↔ u < v ∨ u = v ∧ tie = 0 := by
  by_cases h : u < v
  · simp [orderNat, liftTie, h]
  · by_cases he : u = v <;> simp [orderNat, liftTie, h, he]

theorem liftTie_orderNat_eq_one (tie u v : Nat) :
    liftTie tie (orderNat u v) = 1 ↔ u = v ∧ tie = 1 := by
  by_cases h : u < v
  · have he : u ≠ v := by omega
    simp [orderNat, liftTie, h, he]
  · by_cases he : u = v <;> simp [orderNat, liftTie, h, he]

/-- A concrete pair of strict/equality guards determines the complete
three-way comparison. The tie code is the only finite auxiliary datum. -/
theorem comparison_of_lt_eq (L R U V tie : Nat) (htie : tie ≤ 2)
    (hlt : L < R ↔ U < V ∨ U = V ∧ tie = 0)
    (heq : L = R ↔ U = V ∧ tie = 1) :
    orderNat L R = liftTie tie (orderNat U V) := by
  apply ComparisonProof.orderNat_eq_of_lt_eq L R _
    (ComparisonProof.liftTie_bound tie (orderNat U V) htie
      (ComparisonProof.orderNat_bound U V))
  · exact hlt.trans (liftTie_orderNat_eq_zero tie U V).symm
  · exact heq.trans (liftTie_orderNat_eq_one tie U V).symm

theorem forwardTie_bound (code : Nat) (a b : Letter) (j k : Int) :
    forwardTie code a b j k ≤ 2 := by
  unfold forwardTie
  split_ifs
  · exact ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderNat_bound _ _) (ComparisonProof.orderInt_bound _ _)
  · omega
  · exact ComparisonProof.orderInt_bound _ _
  · exact ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _)
  · exact ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderNat_bound _ _)
      (ComparisonProof.lexOrder_bound _ _
        (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _))
  · exact ComparisonProof.lexOrder_bound _ _
      (ComparisonProof.orderInt_bound _ _) (ComparisonProof.orderInt_bound _ _)
  · omega

theorem headTie_bound (a b : Letter) (j k : Int) :
    headTie a b j k ≤ 2 := by
  unfold headTie
  split
  · unfold reverseOrder
    split_ifs <;> omega
  · exact forwardTie_bound _ _ _ _ _

theorem dispatchTieBound : DispatchTargets.DispatchTieBound := by
  intro A B
  exact headTie_bound _ _ _ _

/-- Case number and orientation, unlike the returned child words, do not
depend on the two prefixes supplied to the canonical selector. -/
theorem head_choice_fields (A : Word) (a : Letter) (B : Word) (b : Letter) :
    (selectHeads A a B b).1 = (selectHeads [] a [] b).1 ∧
    (selectHeads A a B b).2.1 = (selectHeads [] a [] b).2.1 := by
  simp only [selectHeads]
  split_ifs <;> exact ⟨rfl, rfl⟩

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchOrderProof
