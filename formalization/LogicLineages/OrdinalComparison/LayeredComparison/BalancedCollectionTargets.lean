module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection.Targets

def ActualKeyIdentity : Prop := ∀ basis : List Nat, ∀ a b : Atom,
  key basis a=key basis b ↔ keyEqual basis a b

/-- Literal surviving blocks retain original atoms and exact signed block sums. -/
def LiteralCollectedSupport : Prop := ∀ (basis : List Nat) (row : Row),
  (collect basis row).atoms.Pairwise (fun a b => ¬keyEqual basis a.2 b.2) ∧
  (∀ a∈(collect basis row).atoms,
    a.1≠0 ∧ a.1=blockCoefficient basis row (key basis a.2) ∧ ∃ q : Int, (q,a.2)∈row.atoms) ∧
  (wellFormed basis row → wellFormed basis (collect basis row)) ∧
  (genuineHeads row → genuineHeads (collect basis row))

/-- Entire outside remainder is retained, including in the all-cancelled case. -/
def ExactCollectedValue : Prop := ∀ (basis : List Nat) (row : Row),
  (collect basis row).constant=row.constant ∧
  (collect basis row).remainder=row.remainder ∧
  value basis (collect basis row)=value basis row ∧
  remainderValue basis (collect basis row)=remainderValue basis row ∧
  ((collect basis row).atoms=[] → value basis row=remainderValue basis row)

/-- Original L remains usable; the collected row's maxima can only decrease.
No raw-support equality is claimed: original pair support remains ambient data. -/
def OriginalThresholdBudget : Prop := ∀ (basis : List Nat) (row : Row),
  coefficientMass (collect basis row)≤coefficientMass row ∧
  outsideMaximum (collect basis row)=outsideMaximum row ∧
  multiplierMaximum (collect basis row)≤multiplierMaximum row ∧
  offsetMaximum (collect basis row)≤offsetMaximum row ∧
  normMaximum (collect basis row)≤normMaximum row ∧
  threshold (collect basis row)≤threshold row
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection.Targets
