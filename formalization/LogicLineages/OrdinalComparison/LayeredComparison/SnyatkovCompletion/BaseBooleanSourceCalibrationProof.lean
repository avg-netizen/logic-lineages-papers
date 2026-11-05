module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
open BaseBooleanSource

theorem run_append (a b : List CommonHeadCompiler.Instruction) (s : List Nat) :
    Code.run (a ++ b) s = Code.run b (Code.run a s) := by
  simp only [Code.run, List.foldl_append]

theorem literalStackCompiler : BaseBooleanSourceTargets.LiteralStackCompiler := by
  intro p
  induction p with
  | truth => intro s; rfl
  | falsity => intro s; rfl
  | equal a b => intro s; rfl
  | less a b => intro s; rfl
  | negative p ih =>
      intro s
      change Code.run (p.encode ++ [(5, 0, 0)]) s = _
      rw [run_append, ih]
      rfl
  | conjunction p q ihp ihq =>
      intro s
      change Code.run ((p.encode ++ q.encode) ++ [(6, 0, 0)]) s = _
      rw [run_append, run_append, ihp, ihq]
      rfl
  | disjunction p q ihp ihq =>
      intro s
      change Code.run ((p.encode ++ q.encode) ++ [(7, 0, 0)]) s = _
      rw [run_append, run_append, ihp, ihq]
      rfl

theorem literalCompiler : BaseBooleanSourceTargets.LiteralCompiler := by
  intro p
  rw [Code.compile, literalStackCompiler p []]
  rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
