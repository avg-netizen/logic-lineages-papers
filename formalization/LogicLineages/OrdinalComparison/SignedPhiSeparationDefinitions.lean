module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionDefinitions
public import LogicLineages.OrdinalComparison.ControlDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedPhiSeparation

abbrev Row := SignedShiftCollection.Row
open SignedShiftCollection

/-- Exactly the surviving blocks STRICTLY BELOW the actual greatest key.
The leading block is excluded; cancelled blocks are already absent. -/
def lowerRow (row : Row) : CommonHeadLargeRow.Row :=
  (collected row).filter (fun a => decide (a.2 < greatestKey row))

/-- The source's A = sum_{b < B} |a_b|, not the total coefficient mass. -/
def lowerMass (row : Row) : Nat :=
  ((lowerRow row).map (fun a => a.1.natAbs)).sum

/-- The exact source shift for a nonempty collection. D is computed from
EVERY original occurrence, including zero coefficients and cancelled blocks.
For an empty collection, use D alone and make no leading-block claim. -/
def delta (row : Row) : Nat :=
  if collected row = [] then domainOffset row
  else max (domainOffset row)
    (((lowerMass row : Int) + 1 - greatestShift row).toNat)

/-- Totalized original argument. The domain target proves that toNat loses
nothing at each original occurrence after the exact delta shift. -/
def argument (t : Nat) (b : Int) : Nat := ((t : Int) + b).toNat

/-- The literal original-occurrence integer combination of the EXISTING Phi.
This definition does not first discard zero coefficients or cancelled blocks. -/
def value (row : Row) (t : Nat) : Int :=
  (row.map (fun a => a.1 * (Phi (argument t a.2) : Int))).sum

def shiftedInput (row : Row) (x : Nat) : Nat := x + delta row

/-- The input for the accepted natural-key collection after using delta.
The domain target proves D <= delta, so the subtraction is exact. -/
def rebasedInput (row : Row) (x : Nat) : Nat :=
  x + (delta row - domainOffset row)

/-- Every original argument in original occurrence order, with multiplicity. -/
def originalArguments (row : Row) (t : Nat) : List Nat :=
  row.map (fun a => argument t a.2)

def shiftedArguments (row : Row) (x : Nat) : List Nat :=
  originalArguments row (shiftedInput row x)

end LogicLineages.OrdinalComparison.SignedPhiSeparation
