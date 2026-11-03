module
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalBudgetCode

/-- Simultaneous literal freeness, head output-two and scalar output-two counts.
Whole-free stopping has priority, and head/scalar collapse clauses differ. -/
def countData (n : Nat) : Bool×Nat×Nat :=
  OrdinalSyntax.fold (fun k => (OrdinalSyntax.headLeafFree k,1,1))
    (fun tag a b => (a.1 && b.1,
      if a.1 && b.1 then 1 else if tag=4 then a.2.1+b.2.1+1 else 1,
      if a.1 && b.1 then 1 else if tag=4 then a.2.2+b.2.2+1
        else if tag=6 then a.2.1+b.2.2 else 1)) n

def secondCode (n : Nat) : Nat := (countData n).2.2

/-- Read the scalar of the actual full assignment of the ORIGINAL body.
The output is the proven original full-box coordinate two, never a replacement
or an enlarged budget. Malformed source assignment failures remain none. -/
def budgetCode (Γ : List Nat) (n : Nat) : Option Nat :=
  (DefaultSourceAssignment.assignmentCode Γ n).map (fun u => secondCode (u.getD 0 0))
end LogicLineages.OrdinalComparison.Source.OriginalBudgetCode
