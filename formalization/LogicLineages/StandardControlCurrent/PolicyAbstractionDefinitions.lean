module
public import LogicLineages.StandardControlCurrent.PolicyPartialDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAbstraction
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

def partialsCode (p : Policy) (level m : Nat) (h : List Nat) : Option (List (List Nat)) :=
  collectLists ((List.range (m+1)).map (fun i => PolicyPartial.run p level i (h.getD i 0)))

def factorCode (level : Nat) (h : List Nat) : Nat :=
  2^(level+1) * (h.map partialSize).sum

def coordinateCode (p : Policy) (level m : Nat) (h : List Nat)
    (ps : List (List Nat)) (j : Nat) : Option Nat := do
  let delta ← if j=0 then
      PolicyShape.repeatCode p (PolicyShape.siteCode .scalarRepeat)
        (factorCode level h) ((ps.getD 0 []).getD 0 0)
    else if j<level+2 then
      PolicyShape.macroCode p (PolicyShape.siteCode .positiveAbstraction) m
        (ps.map (fun xs => xs.getD j 0))
    else some (headClosure (h.getD j 0))
  pure (if j<m+1 then node 4 delta (headClosure (h.getD j 0)) else delta)

def resultCode (p : Policy) (level m : Nat) (h : List Nat)
    (ps : List (List Nat)) : Option (List Nat) :=
  (List.range (max (level+1) m+1)).foldl (fun acc j => do
    let xs ← acc
    let x ← coordinateCode p level m h ps j
    pure (xs++[x])) (some [])

def abstractionCode (p : Policy) (level m : Nat) (h : List Nat) : Option (List Nat) := do
  let ps ← partialsCode p level m h
  resultCode p level m h ps
end LogicLineages.StandardControlCurrent.PolicyAbstraction
