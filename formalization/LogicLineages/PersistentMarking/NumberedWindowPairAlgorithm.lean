module

public import Init

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm

def pair (a b : Nat) := (a+b)*(a+b)+a

def candidates (n : Nat) : List (Nat × Nat) :=
  (List.range (n+1)).flatMap (fun a => (List.range (n+1)).map (fun b => (a,b)))

def decode (n : Nat) : Option (Nat × Nat) :=
  (candidates n).find? (fun p => decide (pair p.1 p.2 = n))

end LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
