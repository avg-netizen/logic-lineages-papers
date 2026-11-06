module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof

theorem orderNat_bound (a b : Nat) : orderNat a b ≤ 2 := by
  unfold orderNat
  split_ifs <;> omega

theorem orderInt_bound (a b : Int) : orderInt a b ≤ 2 := by
  unfold orderInt
  split_ifs <;> omega

@[simp] theorem orderNat_eq_zero (a b : Nat) : orderNat a b = 0 ↔ a < b := by
  unfold orderNat
  split_ifs <;> omega

@[simp] theorem orderNat_eq_one (a b : Nat) : orderNat a b = 1 ↔ a = b := by
  unfold orderNat
  split_ifs <;> omega

@[simp] theorem orderNat_eq_two (a b : Nat) : orderNat a b = 2 ↔ b < a := by
  unfold orderNat
  split_ifs <;> omega

@[simp] theorem orderInt_eq_zero (a b : Int) : orderInt a b = 0 ↔ a < b := by
  unfold orderInt
  split_ifs <;> omega

@[simp] theorem orderInt_eq_one (a b : Int) : orderInt a b = 1 ↔ a = b := by
  unfold orderInt
  split_ifs <;> omega

@[simp] theorem orderInt_eq_two (a b : Int) : orderInt a b = 2 ↔ b < a := by
  unfold orderInt
  split_ifs <;> omega

theorem liftTie_one (outcome : Nat) : liftTie 1 outcome = outcome := by
  by_cases h : outcome = 1 <;> simp [liftTie,h]

theorem liftTie_assoc (a b outcome : Nat) :
    liftTie a (liftTie b outcome) = liftTie (liftTie a b) outcome := by
  by_cases h : outcome = 1 <;> simp [liftTie,h]

theorem liftTie_bound (tie outcome : Nat) (htie : tie ≤ 2) (hout : outcome ≤ 2) :
    liftTie tie outcome ≤ 2 := by
  unfold liftTie
  split_ifs <;> assumption

theorem lexOrder_bound (first second : Nat) (hfirst : first ≤ 2) (hsecond : second ≤ 2) :
    lexOrder first second ≤ 2 := liftTie_bound second first hsecond hfirst

theorem reverseOrder_bound (outcome : Nat) : reverseOrder outcome ≤ 2 := by
  unfold reverseOrder
  split_ifs <;> omega

theorem reverseOrder_orderNat (a b : Nat) :
    reverseOrder (orderNat a b) = orderNat b a := by
  unfold orderNat reverseOrder
  split_ifs <;> omega

theorem reverseOrder_liftTie (tie outcome : Nat) (_htie : tie ≤ 2) (hout : outcome ≤ 2) :
    reverseOrder (liftTie tie outcome) =
      liftTie (reverseOrder tie) (reverseOrder outcome) := by
  have h : outcome = 0 ∨ outcome = 1 ∨ outcome = 2 := by omega
  rcases h with rfl | rfl | rfl <;> simp [liftTie,reverseOrder]

theorem orderNat_eq_of_lt_eq (L R out : Nat) (hout : out ≤ 2)
    (hLt : L < R ↔ out = 0) (hEq : L = R ↔ out = 1) : orderNat L R = out := by
  unfold orderNat
  split_ifs <;> omega

theorem orderNat_cast (a b : Nat) : orderNat a b = orderInt (a : Int) (b : Int) := by
  simp [orderNat,orderInt]

theorem orderInt_sub_zero (a b : Int) : orderInt (a-b) 0 = orderInt a b := by
  unfold orderInt
  split_ifs <;> omega

theorem orderInt_add_left (a b c : Int) : orderInt (c+a) (c+b) = orderInt a b := by
  unfold orderInt
  split_ifs <;> omega

theorem signAtom_iff (sign : Nat) (value : Int) :
    SignAtom sign value ↔ orderInt value 0 = sign := by
  unfold SignAtom orderInt
  split_ifs <;> omega

theorem guardAt_makeGuards (tie desired : Nat) (h : desired ≤ 2) :
    guardAt (makeGuards tie) desired = signFormula tie desired := by
  have hd : desired = 0 ∨ desired = 1 ∨ desired = 2 := by omega
  rcases hd with rfl | rfl | rfl <;> rfl

theorem signFormula_mem (tie desired sign : Nat) :
    sign ∈ signFormula tie desired ↔ sign ≤ 2 ∧ liftTie tie sign = desired := by
  simp only [signFormula,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false,
    decide_eq_true_eq]
  omega

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof
