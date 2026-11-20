module

public import Init

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm

def advance (edge : Nat → Nat → Bool) (vertices seen : List Nat) : List Nat :=
  vertices.filter (fun v => seen.any (fun w => w == v || edge w v))

def rounds (edge : Nat → Nat → Bool) (vertices : List Nat) (seed : Nat) : Nat → List Nat
  | 0 => vertices.filter (fun x => seed == x)
  | n+1 => advance edge vertices (rounds edge vertices seed n)

def members (edge : Nat → Nat → Bool) (vertices : List Nat) (seed : Nat) : List Nat :=
  rounds edge vertices seed vertices.length

def least (edge : Nat → Nat → Bool) (vertices : List Nat) (seed : Nat) := (members edge vertices seed).min?

end LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm
