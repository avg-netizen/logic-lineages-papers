module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
open CommonHeadBoolean

theorem run_append (heads : List Nat) (xs ys : Code.Program) (stack : Code.Stack) :
    Code.run heads (xs ++ ys) stack = Code.run heads ys (Code.run heads xs stack) := List.foldl_append

theorem literalStackCompiler : CommonHeadBooleanTargets.LiteralStackCompiler := by
  intro heads p stack
  induction p generalizing stack with
  | truth => rfl
  | falsity => rfl
  | equal a b => rfl
  | less a b => rfl
  | negative p ih =>
      simp only [Formula.encode, CommonHeadCode.negative, run_append, ih]
      rfl
  | conjunction p q ihp ihq =>
      simp only [Formula.encode, CommonHeadCode.conjunction, run_append, ihp, ihq]
      rfl
  | disjunction p q ihp ihq =>
      simp only [Formula.encode, CommonHeadCode.disjunction, run_append, ihp, ihq]
      rfl

theorem literalCompiler (heads : List Nat) (p : Formula) :
    Code.compile heads p.encode = (translate heads p).encode := by
  rw [Code.compile, literalStackCompiler]
  rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
