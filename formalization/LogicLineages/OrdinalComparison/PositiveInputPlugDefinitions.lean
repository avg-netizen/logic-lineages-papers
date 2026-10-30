module
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def positiveInputPlug : FixedLimitPositiveExpr → Nat → FixedLimitPositiveExpr
  | .constant n, _ => .constant n
  | .input, x => .constant x
  | .add E F, x => .add (positiveInputPlug E x) (positiveInputPlug F x)
  | .head rho E, x => .head rho (positiveInputPlug E x)

/-- Literal bounded-table code substitution; malformed local input tags
other than 1 default to constant zero, not a blanket invalid-code assertion. -/
def encodedPositivePlugStep (x n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then n else if n%4=1 then if n=1 then 4*x else 0 else
    let p := (n/4).unpair
    if n%4=2 then 4*Nat.pair (table.getD p.1 0) (table.getD p.2 0)+2
    else 4*Nat.pair p.1 (table.getD p.2 0)+3

def encodedPositivePlugTable (x : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => encodedPositivePlugTable x n ++
      [encodedPositivePlugStep x n (encodedPositivePlugTable x n)]

def encodedPositivePlug (n x : Nat) : Nat :=
  (encodedPositivePlugTable x (n+1)).getD n 0

noncomputable def encodedPositiveEvaluation (n x : Nat) : Nat :=
  encodedPositiveFoldValue (encodedPositivePlug n x)

end LogicLineages.OrdinalComparison
