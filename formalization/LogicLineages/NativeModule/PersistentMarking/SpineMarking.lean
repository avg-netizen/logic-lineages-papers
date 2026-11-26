module

public import LogicLineages.NativeModule.PersistentMarking.FreeSubstitution

@[expose] public section

namespace LogicLineages.PersistentMarking.Spine

/-- Partial persistent marking follows only the original initial lambda spine.
An already-marked owner is returned literally, with base and extras unchanged. -/
def mark : Expr → Option Expr
  | .free _ _ => none
  | .bound _ _ => none
  | .lam σ body => (mark body).map (.lam σ)
  | .head f base => some (.marked f f.result base .nil)
  | .marked f τ base extras => some (.marked f τ base extras)

def headmark : Expr → Expr
  | .free σ x => .free σ x
  | .bound σ i => .bound σ i
  | .lam σ body => .lam σ (headmark body)
  | .head f base => .marked f f.result base .nil
  | .marked f τ base extras => .marked f τ base extras

end LogicLineages.PersistentMarking.Spine
