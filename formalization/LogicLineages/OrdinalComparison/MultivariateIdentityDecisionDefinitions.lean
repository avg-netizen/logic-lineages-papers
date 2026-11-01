module
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeDefinitions
public import LogicLineages.OrdinalComparison.PositiveUnaryIdentityDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputPlugDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Exact raw hereditary-CNF code of the fresh actual omega coefficient. -/
def positiveVariableHeadCode (cap i : Nat) : Nat :=
  Nat.pair 1 (Nat.pair (cap+i) 0)+1

def positiveVariableProbeCode (cap i : Nat) : Nat :=
  4*Nat.pair (positiveVariableHeadCode cap i) 1+3

def encodedMultivariateProbeStep (cap n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then n else if n%4=1 then positiveVariableProbeCode cap (n/4) else
    let p := (n/4).unpair
    if n%4=2 then 4*Nat.pair (table.getD p.1 0) (table.getD p.2 0)+2
    else 4*Nat.pair p.1 (table.getD p.2 0)+3

def encodedMultivariateProbeTable (cap : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => encodedMultivariateProbeTable cap n ++
      [encodedMultivariateProbeStep cap n (encodedMultivariateProbeTable cap n)]

def encodedMultivariateProbe (cap n : Nat) : Nat :=
  (encodedMultivariateProbeTable cap (n+1)).getD n 0

/-- Finite actual P1 normal-form test after the faithful fresh-head embedding.
This is a pairwise universal-identity decision, not a new definition of the
paper's literal recursively collected multivariate normal form. -/
noncomputable def encodedMultivariateIdentity (n m : Nat) : Bool :=
  encodedPositiveNormalFormsEqual (encodedMultivariateProbe (max n m) n)
    (encodedMultivariateProbe (max n m) m)

noncomputable def encodedMultivariateProbeCounterInput (n m : Nat) : Nat :=
  encodedPositiveCounterInput (encodedMultivariateProbe (max n m) n)
    (encodedMultivariateProbe (max n m) m)

/-- An actual positive coordinate countervaluation when the identity flag is
false. The uniform algorithm computes each requested coordinate; it does
not evaluate an arbitrary semantic valuation or use a search oracle. -/
noncomputable def encodedMultivariateCounterWeight (n m i : Nat) : Nat :=
  encodedPositiveEvaluation (positiveVariableProbeCode (max n m) i)
    (encodedMultivariateProbeCounterInput n m)

end LogicLineages.OrdinalComparison
