module
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions
public import LogicLineages.OrdinalComparison.AdjacentPackedDefinitions
public import LogicLineages.OrdinalComparison.LimitMassFirstDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- One conservative source-syntax budget for the profile compiler's three
actual thresholds. This never compares ordinal norms by ordinal order. -/
def fixedProfileSyntaxBudget : FixedLimitPositiveExpr → Nat
  | .constant n => max 4 n
  | .input => 4
  | .add E F => fixedProfileSyntaxBudget E+fixedProfileSyntaxBudget F+3
  | .head rho E => fixedProfileSyntaxBudget E+Vendor.R1.treeWeight rho.1+1

def encodedProfileSyntaxBudgetStep (n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then max 4 (n/4)
  else if n%4=1 then 4
  else let p := (n/4).unpair
    if n%4=2 then table.getD p.1 4+table.getD p.2 4+3
    else table.getD p.2 4+rawNormCode p.1+1

def encodedProfileSyntaxBudgetTable : Nat → List Nat
  | 0 => []
  | n+1 => encodedProfileSyntaxBudgetTable n ++
      [encodedProfileSyntaxBudgetStep n (encodedProfileSyntaxBudgetTable n)]

def encodedProfileSyntaxBudget (n : Nat) : Nat :=
  (encodedProfileSyntaxBudgetTable (n+1)).getD n 4

/-- A single primitive-recursive bound dominates the ORIGINAL direct,
adjacent and limit-mass thresholds. The original bounds remain unchanged. -/
def encodedProfileSupplierTail (L E : Nat) : Nat :=
  max ((encodedProfileSyntaxBudget E+5)*(encodedProfileSyntaxBudget E+5)) (rawNormCode L+2)

end LogicLineages.OrdinalComparison
