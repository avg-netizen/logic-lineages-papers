module

public import Init

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPair

/-- A concrete polynomial pairing for later actual numerical syntax
codes. The paper leaves the Gödel numbering convention open. -/
def pair (a b : Nat) : Nat := (a+b)*(a+b)+a

/-- Finite exhaustive decoding covers both components through n itself,
and accepts only a check of the exact original polynomial. -/
def pairCandidates (n : Nat) : List (Nat × Nat) :=
  (List.range (n+1)).flatMap (fun a => (List.range (n+1)).map (fun b => (a,b)))

def decode (n : Nat) : Option (Nat × Nat) :=
  (pairCandidates n).find? (fun p => decide (pair p.1 p.2 = n))

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPair
