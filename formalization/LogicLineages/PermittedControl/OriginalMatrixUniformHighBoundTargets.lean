module
public import LogicLineages.PermittedControl.OriginalMatrixPaidOrderRowTargets
public import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixUniformHighBound
open MixedSameRankResidue (encodeWeighted weightedTailCode)
open HeterogeneousSignedMatrixSlice (Row)
open OriginalMatrixPaidCongruence (paidRow)
open OriginalMatrixPaidOrderRow (IsOrder guardBound signBound keptSyntax)

def residueCeiling (B m : Nat) (row : Row) : Nat :=
  row.2.2.foldr (fun t n => max (weightedTailCode B m [encodeWeighted t]) n) 0

/-- Existing explicit per-field thresholds for modular rows; both
of the existing syntax upper bounds for each original order row. -/
def rowCeiling (B r : Nat) (row : Row) : Nat :=
  match row.1 with
  | .congruence m => residueCeiling B m row
  | _ => max (guardBound B r row) (signBound r row)

def ceiling (B r : Nat) (rows : List Row) : Nat :=
  rows.foldr (fun row n => max (rowCeiling B r row) n) 0

def Funds (B r z : Nat) (ρ : Nat → Nat) (row : Row) : Prop :=
  paidRow B ρ row ∧
    (IsOrder row.1 →
      (∀ t ∈ keptSyntax row.2.2, guardBound B r row ≤ ρ t.2.rank) ∧
        signBound r row ≤ ρ z)

/-- This finite ceiling does not depend on a valuation or a terminal
truth outcome. The numeric payment at the least ambient rank is explicit. -/
def ExactUniformHighBound : Prop :=
  (∀ (B r : Nat) (rows : List Row), ∀ row ∈ rows, rowCeiling B r row ≤ ceiling B r rows) ∧
  ∀ (B r z : Nat) (ρ : Nat → Nat) (rows : List Row), Monotone ρ →
    ceiling B r rows ≤ ρ 0 → ∀ row ∈ rows, Funds B r z ρ row

end LogicLineages.PermittedControl.OriginalMatrixUniformHighBound
