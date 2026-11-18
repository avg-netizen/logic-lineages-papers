module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeCalibrationProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSemanticStatementChecks
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.AllocationProof
open OrdinalComparison PolynomialGraphCompletion

 theorem starts_ge (start : Nat) (xs : List (Expr × Nat)) :
    ∀ b ∈ allocate start xs, start ≤ b.start := by
  induction xs generalizing start with
  | nil => simp [allocate]
  | cons x xs ih =>
    intro b hb
    simp only [allocate,List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact le_rfl
    · exact (Nat.le_add_right _ _).trans (ih _ b hb)

 theorem good (n start : Nat) (xs : List (Expr × Nat)) (hn : n ≤ start)
    (hx : InputBound n xs) : AllocationGood n (allocate start xs) := by
  induction xs generalizing start with
  | nil => exact ⟨by simp [allocate],by simp [allocate]⟩
  | cons x xs ih =>
    have ht := ih (start+nodeCount x.1) (hn.trans (Nat.le_add_right _ _))
      (fun y hy => hx y (List.mem_cons_of_mem x hy))
    constructor
    · intro b hb
      simp only [allocate,List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨hn,fun i hi => ((hx x List.mem_cons_self).2 i hi).trans_le hn,
          ((hx x List.mem_cons_self).1).trans_le hn⟩
      · exact ht.1 b hb
    · apply List.Pairwise.cons _ ht.2
      intro b hb
      exact starts_ge _ xs b hb

 theorem preserve (start : Nat) (xs : List (Expr × Nat)) :
    (allocate start xs).map (fun b => (b.term,b.result)) = xs := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp only [allocate,List.map_cons]; rw [ih]; rfl

 theorem numeric (start : Nat) (xs : List (Expr × Nat)) :
    Code.allocate start (xs.map (fun x => (x.1.encode,x.2))) =
      (allocate start xs).map encodeBlock := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    have hc := ExpressionCodeCalibrationProof.instructionCodeCalibration x.1
    simp only [List.map_cons,Code.allocate,allocate,encodeBlock,Block.start,Block.term,Block.result]
    rw [hc.1,hc.2.1,ih]

 theorem full : Targets.FreshCoverage :=
  ⟨fun n xs hx => good n n xs le_rfl hx,preserve,numeric⟩
end LogicLineages.StandardControlCurrent.GraphNetwork.AllocationProof
