module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
open InternalArithmeticPrograms LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

@[simp] theorem vectorTwo (f : Fin 2 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · obtain rfl : j = 0 := Fin.eq_zero j
    simp
    rfl

theorem exactAdditionEvaluation : InternalArithmeticProgramsTargets.ExactAdditionEvaluation := by
  intro x y
  induction x with
  | zero =>
    change y = 0+y
    exact (Nat.zero_add y).symm
  | succ x ih =>
    change Nat.succ (evaluate addition (x ::ᵥ y ::ᵥ List.Vector.nil)) = (x+1)+y
    rw [ih,Nat.succ_add]

theorem exactMultiplicationEvaluation : InternalArithmeticProgramsTargets.ExactMultiplicationEvaluation := by
  intro x y
  induction x with
  | zero =>
    change 0 = 0*y
    exact (Nat.zero_mul y).symm
  | succ x ih =>
    change evaluate addition (List.Vector.ofFn (fun i : Fin 2 =>
      evaluate ((Fin.cons (Program.projection (1 : Fin 3))
        (Fin.cons (Program.projection (2 : Fin 3)) Fin.elim0) : Fin 2 → Program 3) i)
        (x ::ᵥ evaluate multiplication (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ y ::ᵥ List.Vector.nil))) = _
    rw [vectorTwo]
    change evaluate addition (evaluate multiplication (x ::ᵥ y ::ᵥ List.Vector.nil) ::ᵥ y ::ᵥ List.Vector.nil) = _
    rw [exactAdditionEvaluation,ih,Nat.succ_mul]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
