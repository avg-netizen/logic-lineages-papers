module
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal source profile substitution, with binary sums retained. -/
def fixedProfileCompose : FixedLimitPositiveExpr → FixedLimitPositiveExpr → FixedLimitPositiveExpr
  | .constant n, _ => .constant n
  | .input, F => F
  | .add E G, F => .add (fixedProfileCompose E F) (fixedProfileCompose G F)
  | .head rho E, F => .head rho (fixedProfileCompose E F)

def encodedProfileComposeStep (f n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then n else if n%4=1 then if n=1 then f else 0 else
    let p := (n/4).unpair
    if n%4=2 then 4*Nat.pair (table.getD p.1 0) (table.getD p.2 0)+2
    else 4*Nat.pair p.1 (table.getD p.2 0)+3

def encodedProfileComposeTable (f : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => encodedProfileComposeTable f n ++
      [encodedProfileComposeStep f n (encodedProfileComposeTable f n)]

def encodedProfileCompose (n f : Nat) : Nat :=
  (encodedProfileComposeTable f (n+1)).getD n 0

end LogicLineages.OrdinalComparison
