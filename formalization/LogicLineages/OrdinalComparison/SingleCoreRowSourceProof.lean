module
public import LogicLineages.OrdinalComparison.SingleCoreRowTargets
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayProof
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreRowCompiler

theorem multiple_code (n : Nat) (E : FixedLimitPositiveExpr) :
    encodedPositiveSourceMultiple n (positiveExprEncode E)=positiveExprEncode (positiveSourceMultiple n E) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodedPositiveSourceMultiple,positiveSourceMultiple,positiveExprEncode,ih]

theorem multiple_value (n : Nat) (E : FixedLimitPositiveExpr) (t : Nat) :
    actualFixedLimitProfileEval (positiveSourceMultiple n E) t=n*actualFixedLimitProfileEval E t := by
  induction n with
  | zero => simp [positiveSourceMultiple,actualFixedLimitProfileEval]
  | succ n ih => simp only [positiveSourceMultiple,actualFixedLimitProfileEval,ih,Nat.succ_mul]

theorem multiple_valid (n : Nat) (E : FixedLimitPositiveExpr) (hE : fixedLimitProfileBelow epsilonZero E) :
    fixedLimitProfileBelow epsilonZero (positiveSourceMultiple n E) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,hE⟩

theorem atom_code (atom : SingleCoreRowAtom) :
    encodedSingleCoreAtomPositive (singleCoreAtomCode atom)=positiveExprEncode (singleCoreAtomPositive atom) := by
  simp only [encodedSingleCoreAtomPositive,singleCoreAtomCode,singleCoreAtomPositive,positiveExprEncode,
    MultivariatePositiveRay.source.1 atom.multiplier]

theorem atom_value (atom : SingleCoreRowAtom) (t : Nat) :
    actualFixedLimitProfileEval (singleCoreAtomPositive atom) t=
      actualProfileHead atom.head (atom.multiplier*t+atom.offset) := by
  simp only [singleCoreAtomPositive,actualFixedLimitProfileEval,MultivariatePositiveRay.source.2.1 atom.multiplier t]

theorem atom_valid (atom : SingleCoreRowAtom) (hl : Order.IsSuccLimit atom.head.1.repr) :
    fixedLimitProfileBelow epsilonZero (singleCoreAtomPositive atom) :=
  ⟨hl,normalRepresentationSound atom.head,MultivariatePositiveRay.source.2.2.1 atom.multiplier,True.intro⟩

private theorem fold_code (negative : Bool) (atoms : List SingleCoreRowAtom) :
    (atoms.map singleCoreAtomCode).foldr (fun atom rest =>
      4*Nat.pair (encodedPositiveSourceMultiple (if negative then atom.2.1.2 else atom.2.1.1)
        (encodedSingleCoreAtomPositive atom)) rest+2) 0=
      positiveExprEncode (atoms.foldr (fun atom rest =>
        .add (positiveSourceMultiple (singleCoreCoefficientPart negative atom.coefficient)
          (singleCoreAtomPositive atom)) rest) (.constant 0)) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    simp only [List.map_cons,List.foldr_cons,atom_code,←multiple_code,positiveExprEncode,ih]
    cases negative <;> rfl

theorem part_code (negative : Bool) (row : SingleCoreRow) :
    encodedSingleCoreRowPart negative (singleCoreRowCode row)=positiveExprEncode (singleCoreRowPart negative row) := by
  simp only [encodedSingleCoreRowPart,singleCoreRowCode,singleCoreRowPart,positiveExprEncode,
    MultivariatePositiveRay.source.1,fold_code,singleCoreCoefficientCode,singleCoreCoefficientPart]

theorem part_valid (negative : Bool) (row : SingleCoreRow) (hv : singleCoreRowValid row) :
    fixedLimitProfileBelow epsilonZero (singleCoreRowPart negative row) := by
  refine ⟨True.intro,MultivariatePositiveRay.source.2.2.1 _,?_⟩
  have h : ∀ atoms : List SingleCoreRowAtom,
      (∀ atom∈atoms,Order.IsSuccLimit atom.head.1.repr) →
      fixedLimitProfileBelow epsilonZero (atoms.foldr (fun atom rest =>
        .add (positiveSourceMultiple (singleCoreCoefficientPart negative atom.coefficient)
          (singleCoreAtomPositive atom)) rest) (.constant 0)) := by
    intro atoms h
    induction atoms with
    | nil => trivial
    | cons atom rest ih =>
      exact ⟨multiple_valid _ _ (atom_valid atom (h atom List.mem_cons_self)),
        ih (fun a ha => h a (List.mem_cons_of_mem _ ha))⟩
  exact h row.atoms (fun atom hm => (hv atom hm).1)

private theorem fold_value (negative : Bool) (atoms : List SingleCoreRowAtom) (t : Nat) :
    (actualFixedLimitProfileEval (atoms.foldr (fun atom rest =>
        .add (positiveSourceMultiple (singleCoreCoefficientPart negative atom.coefficient)
          (singleCoreAtomPositive atom)) rest) (.constant 0)) t : Int)=
      (atoms.map (fun atom => (singleCoreCoefficientPart negative atom.coefficient : Int)*
        (actualProfileHead atom.head (atom.multiplier*t+atom.offset) : Int))).sum := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    simp only [List.foldr_cons,actualFixedLimitProfileEval,List.map_cons,List.sum_cons,
      Nat.cast_add,multiple_value,Nat.cast_mul,atom_value,ih]

theorem part_value (negative : Bool) (row : SingleCoreRow) (t : Nat) :
    (actualFixedLimitProfileEval (singleCoreRowPart negative row) t : Int)=
      (singleCoreCoefficientPart negative row.constant : Int)+
      (singleCoreCoefficientPart negative row.linear : Int)*(t : Int)+
      (row.atoms.map (fun atom => (singleCoreCoefficientPart negative atom.coefficient : Int)*
        (actualProfileHead atom.head (atom.multiplier*t+atom.offset) : Int))).sum := by
  simp only [singleCoreRowPart,actualFixedLimitProfileEval,Nat.cast_add,
    MultivariatePositiveRay.source.2.1,Nat.cast_mul,fold_value]
  ring

private theorem atom_sum_difference (atoms : List SingleCoreRowAtom) (t : Nat) :
    (atoms.map (fun atom => (singleCoreCoefficientPart false atom.coefficient : Int)*
      (actualProfileHead atom.head (atom.multiplier*t+atom.offset) : Int))).sum-
    (atoms.map (fun atom => (singleCoreCoefficientPart true atom.coefficient : Int)*
      (actualProfileHead atom.head (atom.multiplier*t+atom.offset) : Int))).sum=
      (atoms.map (fun atom => atom.coefficient*
        (actualProfileHead atom.head (atom.multiplier*t+atom.offset) : Int))).sum := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [show ∀ a b c d : Int,(a+b)-(c+d)=(a-c)+(b-d) by intros; ring,ih,←sub_mul]
    simp only [singleCoreCoefficientPart,Bool.false_eq_true,if_false,if_true,Int.toNat_sub_toNat_neg]

theorem semantics : Targets.ActualSingleCoreRowPartsSemantics := by
  intro row hv
  refine ⟨part_valid false row hv,part_valid true row hv,?_⟩
  intro t
  rw [part_value,part_value]
  have hk := Int.toNat_sub_toNat_neg row.constant
  have hr := Int.toNat_sub_toNat_neg row.linear
  have hs := atom_sum_difference row.atoms t
  simp only [singleCoreCoefficientPart,Bool.false_eq_true,if_false,if_true] at hs ⊢
  unfold actualSingleCoreRowValue
  rw [show ∀ a b c d e f : Int,(a+b+c)-(d+e+f)=(a-d)+(b-e)+(c-f) by intros; ring,
    ←sub_mul,hk,hr,hs]

end LogicLineages.OrdinalComparison.SingleCoreRowCompiler
