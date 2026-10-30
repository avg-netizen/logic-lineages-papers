module
public import LogicLineages.OrdinalComparison.EncodedCollectedMergeDefinitions
public import LogicLineages.OrdinalComparison.CollectedNormalizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Root-field support detector; its source meaning is restricted to valid
collected forms, whose tag arguments are all open and coefficients positive. -/
def encodedCollectedOpen (n : Nat) : Bool :=
  (n.unpair.2.unpair.1 != 0) || (n.unpair.2.unpair.2 != 0)

def encodedCollectedConstant (n : Nat) : Nat := Nat.pair n (Nat.pair 0 0)

/-- Local malformed branches default to the zero form. A composite malformed
code is not claimed to have that same output. -/
noncomputable def encodedCollectedNormalizeStep (n : Nat) (table : List Nat) : Nat :=
  if n%4=0 then encodedCollectedConstant (n/4)
  else if n%4=1 then
    if n=1 then Nat.pair 0 (Nat.pair 1 0) else encodedCollectedConstant 0
  else
    let p := (n/4).unpair
    if n%4=2 then encodedCollectedAdd (table.getD p.1 0) (table.getD p.2 0)
    else if rawNormalCode p.1=1 then
      let arg := table.getD p.2 0
      if encodedCollectedOpen arg=false then encodedCollectedConstant (encodedPositiveFoldValue n)
      else Nat.pair 0 (Nat.pair 0 (encodedCollectedCons (Nat.pair p.1 arg) 1 0))
    else encodedCollectedConstant 0

noncomputable def encodedCollectedNormalizeTable : Nat → List Nat
  | 0 => []
  | n+1 => encodedCollectedNormalizeTable n ++
      [encodedCollectedNormalizeStep n (encodedCollectedNormalizeTable n)]

noncomputable def encodedCollectedNormalize (n : Nat) : Nat :=
  (encodedCollectedNormalizeTable (n+1)).getD n 0

end LogicLineages.OrdinalComparison
