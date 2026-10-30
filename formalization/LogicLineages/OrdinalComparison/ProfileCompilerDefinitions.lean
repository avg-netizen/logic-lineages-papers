module
public import LogicLineages.OrdinalComparison.ProfileHeadDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal one-variable positive source trees; validity of a fixed head is
separate. Binary addition is retained, not a weighted graph shorthand. -/
inductive FixedLimitPositiveExpr where
  | constant : Nat → FixedLimitPositiveExpr
  | input : FixedLimitPositiveExpr
  | add : FixedLimitPositiveExpr → FixedLimitPositiveExpr → FixedLimitPositiveExpr
  | head : NONote → FixedLimitPositiveExpr → FixedLimitPositiveExpr

def fixedLimitProfileBelow (L : Ordinal) : FixedLimitPositiveExpr → Prop
  | .constant _ => True
  | .input => True
  | .add E F => fixedLimitProfileBelow L E ∧ fixedLimitProfileBelow L F
  | .head rho E => Order.IsSuccLimit rho.1.repr ∧ rho.1.repr < L ∧ fixedLimitProfileBelow L E

noncomputable def actualFixedLimitProfileEval : FixedLimitPositiveExpr → Nat → Nat
  | .constant n, _ => n
  | .input, x => x
  | .add E F, x => actualFixedLimitProfileEval E x + actualFixedLimitProfileEval F x
  | .head rho E, x => actualProfileHead rho (actualFixedLimitProfileEval E x)

/-- Executable threshold paying all constants and binary fan-in. -/
def fixedLimitProfileThreshold : FixedLimitPositiveExpr → Nat
  | .constant n => max 4 n
  | .input => 4
  | .add E F => max (fixedLimitProfileThreshold E) (fixedLimitProfileThreshold F)
  | .head _ E => fixedLimitProfileThreshold E

/-- Tree traversal may duplicate a shared graph subexpression; no graph-sharing
complexity claim is made. Each addition appends one actual omega head. -/
def profileBoundWordInternal : FixedLimitPositiveExpr → List NONote
  | .constant _ => []
  | .input => []
  | .add E F => profileBoundWordInternal E ++ profileBoundWordInternal F ++ [profileOmegaNote]
  | .head rho E => profileBoundWordInternal E ++ [rho]

def profileBoundWord (E : FixedLimitPositiveExpr) : List NONote :=
  profileBoundWordInternal E ++ [profileOmegaNote]

/-- Actual semantic action, distinct from the executable word compiler. -/
noncomputable def actualProfileWordValue : List NONote → Nat → Nat
  | [], x => x
  | rho :: w, x => actualProfileWordValue w (actualProfileHead rho x)

end LogicLineages.OrdinalComparison
