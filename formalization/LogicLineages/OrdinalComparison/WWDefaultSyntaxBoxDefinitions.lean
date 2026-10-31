module
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

def defaultBoxTailCode (n f g : Nat) : Nat :=
  if n=0 then node 4 f g else node 4 f (node 4 g (repeatCode n 1))

def defaultApplicationCode (resultLevel argLevel : Nat) (f g : List Nat) : List Nat :=
  (List.range (resultLevel+1)).map (fun i => if i=0 then
    node 6 (boxPositive argLevel f g 1) (defaultBoxTailCode argLevel (f.getD 0 0) (g.getD 0 0))
    else boxPositive argLevel f g i)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
