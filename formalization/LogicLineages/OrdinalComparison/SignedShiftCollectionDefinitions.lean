module
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection

/-- Literal input occurrences: an integer coefficient and an INTEGER shift.
Zero coefficients and occurrences whose blocks later cancel remain here. -/
abbrev Row := List (Int × Int)

/-- The least nonnegative domain offset, computed BEFORE collection from
EVERY original occurrence. The empty row has offset zero. -/
def domainOffset (row : Row) : Nat :=
  (row.map (fun a => (-a.2).toNat)).foldl max 0

/-- Order-preserving natural key on the original shifts, not Int's encoding.
The total extension to other integers may truncate; no global injectivity
of this extension is asserted. -/
def rebaseKey (row : Row) (b : Int) : Nat :=
  ((domainOffset row : Int) + b).toNat

/-- Explicit signed interpretation of a rebased natural key. -/
def originalShift (row : Row) (k : Nat) : Int :=
  (k : Int) - (domainOffset row : Int)

/-- Rebase every original occurrence, with its coefficient unchanged. -/
def rebaseRow (row : Row) : CommonHeadLargeRow.Row :=
  row.map (fun a => (a.1, rebaseKey row a.2))

/-- The EXISTING literal equal-key collector, applied to the rebased row. -/
def collected (row : Row) : CommonHeadLargeRow.Row :=
  CommonHeadCollectedRow.collect (rebaseRow row)

/-- The actual sum of coefficients at the specified signed shift. -/
def coefficient (row : Row) (b : Int) : Int :=
  (row.map (fun a => if a.2 = b then a.1 else 0)).sum

/-- Arbitrary evaluators on the original signed shifts. -/
def weighted (f : Int → Int) (row : Row) : Int :=
  (row.map (fun a => a.1 * f a.2)).sum

/-- Actual finite maximum of the surviving natural keys. Its empty default
is zero; it denotes a surviving key only under the nonempty premise. -/
def greatestKey (row : Row) : Nat :=
  ((collected row).map Prod.snd).foldl max 0

def greatestShift (row : Row) : Int :=
  originalShift row (greatestKey row)

def leadingCoefficient (row : Row) : Int :=
  coefficient row (greatestShift row)

end LogicLineages.OrdinalComparison.SignedShiftCollection
