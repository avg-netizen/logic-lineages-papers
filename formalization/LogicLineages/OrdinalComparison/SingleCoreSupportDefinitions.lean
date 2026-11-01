module
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal raw-variable support of the full arbitrary nested positive core.
Duplicates are retained; no semantic independence or range-surjectivity is
asserted. Zero multiples are represented by their actual constant-zero tree. -/
def singleCoreSupport : MultivariatePositiveExpr → List Nat
  | .constant _ => []
  | .input i => [i]
  | .add E F => singleCoreSupport E++singleCoreSupport F
  | .head _ E => singleCoreSupport E

def encodedSingleCoreSupportStep (n : Nat) (table : List (List Nat)) : List Nat :=
  if n%4=0 then [] else if n%4=1 then [n/4] else
    let p := (n/4).unpair
    if n%4=2 then table.getD p.1 []++table.getD p.2 [] else table.getD p.2 []

def encodedSingleCoreSupportTable : Nat → List (List Nat)
  | 0 => []
  | n+1 => encodedSingleCoreSupportTable n++[encodedSingleCoreSupportStep n (encodedSingleCoreSupportTable n)]

def encodedSingleCoreSupport (n : Nat) : List Nat := (encodedSingleCoreSupportTable (n+1)).getD n []

end LogicLineages.OrdinalComparison
