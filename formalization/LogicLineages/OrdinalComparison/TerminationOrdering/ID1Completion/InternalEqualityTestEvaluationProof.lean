module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
open InternalEqualityTest LogicLineages.ComputabilityKnowledge
open GorbowPRProgram List.Vector

@[simp] theorem vectorOne (f : Fin 1 → Nat) : List.Vector.ofFn f = f 0 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  simp

@[simp] theorem vectorTwo (f : Fin 2 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp <;> rfl
  · obtain rfl : j = 0 := Fin.eq_zero j
    simp <;> rfl

@[simp] theorem vectorThree (f : Fin 3 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp <;> rfl
  · simp <;> rfl
  · obtain rfl : k = 0 := Fin.eq_zero k
    simp <;> rfl

theorem exactPredecessorEvaluation : InternalEqualityTestTargets.ExactPredecessorEvaluation := by
  intro x
  cases x <;> rfl

theorem exactSubtractionEvaluation : InternalEqualityTestTargets.ExactSubtractionEvaluation := by
  intro x y
  induction x with
  | zero => rfl
  | succ x ih =>
    change evaluate predecessor (List.Vector.ofFn (fun _ : Fin 1 =>
      evaluate subtract (x ::ᵥ y ::ᵥ List.Vector.nil))) = y - (x+1)
    rw [vectorOne,exactPredecessorEvaluation,ih]
    rw [Nat.pred_eq_sub_one]
    omega

theorem zeroTestEvaluation (x : Nat) :
    evaluate GorbowPRInternalControl.zeroTest (x ::ᵥ List.Vector.nil) = if x = 0 then 1 else 0 := by
  cases x with
  | zero => simp [GorbowPRInternalControl.zeroTest,GorbowPRInternalControl.one,evaluate]
  | succ x => simp [GorbowPRInternalControl.zeroTest,GorbowPRInternalControl.zeroStep,evaluate]

theorem conditionalEvaluation (x a b : Nat) :
    evaluate GorbowPRInternalControl.conditional (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) =
      if x = 0 then a else b := by
  cases x <;> rfl

theorem reverseEvaluation (x y : Nat) :
    evaluate reverseSubtract (x ::ᵥ y ::ᵥ List.Vector.nil) = x-y := by
  change evaluate subtract (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (Program.projection (1 : Fin 2))
      (Fin.cons (Program.projection (0 : Fin 2)) Fin.elim0) : Fin 2 → Program 2) i) (x ::ᵥ y ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  exact exactSubtractionEvaluation y x

theorem reverseZeroEvaluation (x y : Nat) :
    evaluate reverseZeroTest (x ::ᵥ y ::ᵥ List.Vector.nil) = if x-y = 0 then 1 else 0 := by
  change evaluate GorbowPRInternalControl.zeroTest (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate reverseSubtract (x ::ᵥ y ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,zeroTestEvaluation,reverseEvaluation]

theorem exactEqualityEvaluation : InternalEqualityTestTargets.ExactEqualityEvaluation := by
  intro x y
  change evaluate GorbowPRInternalControl.conditional (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((Fin.cons subtract (Fin.cons reverseZeroTest (Fin.cons zeroBinary Fin.elim0)) : Fin 3 → Program 2) i)
      (x ::ᵥ y ::ᵥ List.Vector.nil)) = _
  rw [vectorThree]
  change evaluate GorbowPRInternalControl.conditional
    (evaluate subtract (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ
      evaluate reverseZeroTest (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ 0 ::ᵥ List.Vector.nil) = _
  rw [conditionalEvaluation,exactSubtractionEvaluation,reverseZeroEvaluation]
  split_ifs <;> omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
