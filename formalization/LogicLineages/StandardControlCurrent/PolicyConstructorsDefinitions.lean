module
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyConstructors
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

def onesCode (level : Nat) : List Nat := List.replicate (level+1) 1

def recursorCode (p : Policy) (inputLevel resultLevel : Nat) : Option (List Nat) := do
  let two ← PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) 2 1
  pure ((List.range (resultLevel+1)).map (fun i =>
    if i=0 then two else if i=inputLevel+2 then 2 else 1))

def boxTailCode (p : Policy) (n f g : Nat) : Option Nat :=
  if n=0 then some (node 4 f g) else do
    let num ← PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) n 1
    PolicyShape.macroCode p (PolicyShape.siteCode .optionalBoxTail) 2 [f,g,num]

def applicationCode (p : Policy) (resultLevel argLevel : Nat)
    (f g : List Nat) : Option (List Nat) := do
  let tail ← boxTailCode p argLevel (f.getD 0 0) (g.getD 0 0)
  pure ((List.range (resultLevel+1)).map (fun i => if i=0 then
    node 6 (boxPositive argLevel f g 1) tail else boxPositive argLevel f g i))
end LogicLineages.StandardControlCurrent.PolicyConstructors
