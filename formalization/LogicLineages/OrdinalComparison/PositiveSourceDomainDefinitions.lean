module
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramDefinitions
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Genuine source-head test: faithful normal note, nonzero code, and zero
actual finite remainder. Parsing raw NF alone is insufficient. -/
def encodedPositiveHeadDomain (rho : Nat) : Nat :=
  if rawNormalCode rho=1 ∧ rho≠0 ∧ encodedOrdinalFiniteRemainder rho=0 then 1 else 0

/-- Source-valid flag and literal input-occurrence flag. Both flags are
numeric0/1, with arbitrary malformed local codes handled explicitly. -/
def encodedPositiveSourceDataStep (n : Nat) (table : List (Nat × Nat)) : Nat × Nat :=
  if n%4=0 then (1,0)
  else if n%4=1 then if n=1 then (1,1) else (0,0)
  else let p := (n/4).unpair
    let a := table.getD p.1 (0,0)
    let b := table.getD p.2 (0,0)
    if n%4=2 then
      (if a.1=1 ∧ b.1=1 then 1 else 0,if a.2=1 ∨ b.2=1 then 1 else 0)
    else (if encodedPositiveHeadDomain p.1=1 ∧ b.1=1 then 1 else 0,b.2)

def encodedPositiveSourceDataTable : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 => encodedPositiveSourceDataTable n ++
      [encodedPositiveSourceDataStep n (encodedPositiveSourceDataTable n)]

def encodedPositiveSourceData (n : Nat) : Nat × Nat :=
  (encodedPositiveSourceDataTable (n+1)).getD n (0,0)

end LogicLineages.OrdinalComparison
