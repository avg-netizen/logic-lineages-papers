module
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputSupportDefinitions
public import LogicLineages.OrdinalComparison.EncodedFiniteTailDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- One bottom-up evaluation entry. Malformed local tags default to zero;
this does not assert that every malformed composite tree evaluates to zero. -/
def encodedPositiveFoldStep (n : Nat) (table : List Nat) : Part Nat :=
  if n%4=0 then Part.some (n/4)
  else if n%4=1 then Part.some 0
  else
    let p := (n/4).unpair
    if n%4=2 then Part.some (table.getD p.1 0 + table.getD p.2 0)
    else if rawNormalCode p.1=1 then
      encodedCollapsePartial (encodedFiniteTail p.1 (table.getD p.2 0))
    else Part.some 0

/-- Entries are appended in code order, so all recursive child codes precede
an actual add/head entry. Actual collapse, not a semantic oracle, is invoked. -/
def encodedPositiveFoldTable : Nat → Part (List Nat)
  | 0 => Part.some []
  | n+1 => (encodedPositiveFoldTable n).bind fun table =>
      (encodedPositiveFoldStep n table).map fun value => table ++ [value]

def encodedPositiveFoldProgram (n : Nat) : Part Nat :=
  (encodedPositiveFoldTable (n+1)).map fun table => table.getD n 0

/-- Honest total wrapper; uniform computability is a separate theorem. -/
noncomputable def encodedPositiveFoldValue (n : Nat) : Nat :=
  by classical exact (encodedPositiveFoldProgram n).getOrElse 0

end LogicLineages.OrdinalComparison
