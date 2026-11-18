import LogicLineages.PersistentMarking.SpineSyntax
namespace LogicLineages.PersistentMarking.Spine

/-- Sequential actual unary calls, distinct from the original full-call semantics.
No converse from successful staging to successful original calling is asserted. -/
def unaryCalls (q : Expr) (args : Args) : Option Expr :=
  match args with
  | .nil => some q
  | .cons a rest => (apply q (.cons a .nil)).bind (fun r => unaryCalls r rest)
termination_by args
end LogicLineages.PersistentMarking.Spine
