module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

/-- Zero padding only outside the actual list length. -/
def boxPositive (n : Nat) (f g : List Nat) (i : Nat) : Nat :=
  if h : i ≤ n then node 5 (boxPositive n f g (i+1)) (node 4 (f.getD i 0) (g.getD i 0))
  else f.getD i 0
termination_by n+1-i
decreasing_by omega

def boxTail (n : Nat) (f g : Nat) : Nat :=
  if n=0 then node 4 f g else node 4 (node 4 f g) (repeatCode n 1)

def applicationCode (resultLevel argLevel : Nat) (f g : List Nat) : List Nat :=
  (List.range (resultLevel+1)).map (fun i => if i=0 then
    node 6 (boxPositive argLevel f g 1) (boxTail argLevel (f.getD 0 0) (g.getD 0 0))
    else boxPositive argLevel f g i)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
