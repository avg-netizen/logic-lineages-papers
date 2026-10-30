module

public import LogicLineages.OrdinalComparison.RestrictedPartitionDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
/-! Paper08's effective restricted-partition calculation (kernel-residue proof),
using paper10's actual weighted-vector cardinality as the semantic count.
The executable rows are independent raw finite data. k=0 has the explicit
identity-lookup convention; only positive k occurs in the degree recursion. -/
namespace LogicLineages.OrdinalComparison

def restrictedPartitionRowEntry (k : Nat) (previous : List Nat) (n : Nat) : Nat :=
  if k = 0 then previous.getD n 0 else
    ((List.range (n / k + 1)).map (fun j => previous.getD (n - k * j) 0)).foldr (· + ·) 0

def restrictedPartitionRowStep (k : Nat) (previous : List Nat) : List Nat :=
  (List.range previous.length).map (restrictedPartitionRowEntry k previous)

def restrictedPartitionRows (bound : Nat) : Nat → List Nat
  | 0 => (List.range (bound + 1)).map (fun n => if n = 0 then 1 else 0)
  | d + 1 => restrictedPartitionRowStep (d + 1) (restrictedPartitionRows bound d)

def restrictedPartitionEval (d n : Nat) : Nat := (restrictedPartitionRows n d).getD n 0

end LogicLineages.OrdinalComparison
