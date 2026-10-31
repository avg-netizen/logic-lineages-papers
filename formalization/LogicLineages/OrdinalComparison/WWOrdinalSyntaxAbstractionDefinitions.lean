module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

def collectLists : List (Option (List Nat)) → Option (List (List Nat))
  | [] => some []
  | a::rest => do
    let x ← a
    let xs ← collectLists rest
    pure (x::xs)

def partialsCode (level m : Nat) (h : List Nat) : Option (List (List Nat)) :=
  collectLists ((List.range (m+1)).map (fun i => partialRun level i (h.getD i 0)))

def abstractionResult (level m : Nat) (h : List Nat) (ps : List (List Nat)) : List Nat :=
  let factor := 2^(level+1) * (h.map partialSize).sum
  (List.range (max (level+1) m + 1)).map (fun j =>
    let delta := if j=0 then repeatCode factor ((ps.getD 0 []).getD 0 0)
      else if j<level+2 then sumPrefix m (ps.map (fun p => p.getD j 0))
      else headClosure (h.getD j 0)
    if j<m+1 then node 4 delta (headClosure (h.getD j 0)) else delta)

def abstractionCode (level m : Nat) (h : List Nat) : Option (List Nat) :=
  (partialsCode level m h).map (abstractionResult level m h)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
