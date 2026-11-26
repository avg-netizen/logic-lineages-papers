module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionDefinitions
public import LogicLineages.PermittedControl.LiteralCovarianceDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.NakedDeltaProgram
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open StandardControlCurrent

/-- The inner delta coordinate only, without retained-head addition. -/
def coordinateCode (p : Policy) (level m : Nat) (h : List Nat)
    (ps : List (List Nat)) (j : Nat) : Option Nat :=
  if j=0 then PolicyShape.repeatCode p (PolicyShape.siteCode .scalarRepeat)
    (PolicyAbstraction.factorCode level h) ((ps.getD 0 []).getD 0 0)
  else if j<level+2 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveAbstraction) m
    (ps.map (fun xs => xs.getD j 0))
  else some (headClosure (h.getD j 0))

def resultCode (p : Policy) (level m : Nat) (h : List Nat)
    (ps : List (List Nat)) : Option (List Nat) :=
  (List.range (max (level+1) m+1)).foldl (fun acc j => do
    let xs ← acc
    let x ← coordinateCode p level m h ps j
    pure (xs++[x])) (some [])

def deltaCode (p : Policy) (level m : Nat) (h : List Nat) : Option (List Nat) := do
  let ps ← PolicyAbstraction.partialsCode p level m h
  resultCode p level m h ps

end LogicLineages.PermittedControl.NakedDeltaProgram
