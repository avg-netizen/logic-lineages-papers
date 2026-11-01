module
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal source P_d syntax, with an explicit numeric variable index. The
finite variable bound and actual limit-head domain are separate predicates. -/
inductive MultivariatePositiveExpr where
  | constant : Nat → MultivariatePositiveExpr
  | input : Nat → MultivariatePositiveExpr
  | add : MultivariatePositiveExpr → MultivariatePositiveExpr → MultivariatePositiveExpr
  | head : NONote → MultivariatePositiveExpr → MultivariatePositiveExpr

def multivariatePositiveValid (d : Nat) : MultivariatePositiveExpr → Prop
  | .constant _ => True
  | .input i => i<d
  | .add E F => multivariatePositiveValid d E ∧ multivariatePositiveValid d F
  | .head rho E => Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
      multivariatePositiveValid d E

noncomputable def actualMultivariatePositiveEval : MultivariatePositiveExpr → (Nat → Nat) → Nat
  | .constant c, _ => c
  | .input i, ρ => ρ i
  | .add E F, ρ => actualMultivariatePositiveEval E ρ + actualMultivariatePositiveEval F ρ
  | .head rho E, ρ => actualProfileHead rho (actualMultivariatePositiveEval E ρ)

def multivariatePositiveEncode : MultivariatePositiveExpr → Nat
  | .constant c => 4*c
  | .input i => 4*i+1
  | .add E F => 4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2
  | .head rho E => 4*Nat.pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)+3

/-- A literal repeated-input tree; zero multiplicity is the actual constant0.
No multiplication of two open values is added to the source grammar. -/
def positiveInputMultiple : Nat → FixedLimitPositiveExpr
  | 0 => .constant 0
  | n+1 => .add (positiveInputMultiple n) .input

def positiveInputMultipleCode : Nat → Nat
  | 0 => 0
  | n+1 => 4*Nat.pair (positiveInputMultipleCode n) 1+2

/-- The source weighted ray uses weights 1,B,B²,..., without changing any
head, closed constant, addition node or shared variable occurrence. -/
def multivariatePositiveRay (base : Nat) : MultivariatePositiveExpr → FixedLimitPositiveExpr
  | .constant c => .constant c
  | .input i => positiveInputMultiple (base^i)
  | .add E F => .add (multivariatePositiveRay base E) (multivariatePositiveRay base F)
  | .head rho E => .head rho (multivariatePositiveRay base E)

/-- Numeric bounded-table fold implementing exactly the weighted-ray tree.
The total operation is specified on every code; source correctness below
does not impose a compiler-image restriction on the source trees. -/
def encodedMultivariateRayStep (base n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then n else if n%4=1 then positiveInputMultipleCode (base^(n/4)) else
    let p := (n/4).unpair
    if n%4=2 then 4*Nat.pair (table.getD p.1 0) (table.getD p.2 0)+2
    else 4*Nat.pair p.1 (table.getD p.2 0)+3

def encodedMultivariateRayTable (base : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => encodedMultivariateRayTable base n ++
      [encodedMultivariateRayStep base n (encodedMultivariateRayTable base n)]

def encodedMultivariateRay (base n : Nat) : Nat :=
  (encodedMultivariateRayTable base (n+1)).getD n 0

end LogicLineages.OrdinalComparison
