module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitness

/-- Current finite valuation, original binder name, and original raw body code. -/
abbrev Input := List Nat × (Nat × Nat)

def parent (p : Input) : Nat := 5 * Nat.pair p.2.1 p.2.2 + 4

def need (p : Input) : Bool := decide (FiniteSearchPrograms.Code.decide p.1 (parent p) = some true)

/-- Unsupported or false parents make the search terminate immediately.
True parents search increasing original-name assignments using the actual body
algorithm and exact current-environment update. -/
def hit (p : Input) (n : Nat) : Bool :=
  !need p || FiniteSearchPrograms.Code.answer (BoundedSourcePrograms.Code.update p.1 p.2.1 n) p.2.2

def search (p : Input) : Part Nat := Nat.rfind (fun n => Part.some (hit p n))

/-- Fixed totalization of the concrete recursive search. The default branch is
not assumed unreachable: global termination and actual computability are targets. -/
noncomputable def result (p : Input) : Nat := by
  classical
  exact (search p).getOrElse 0

noncomputable def witness (p : Input) : Option Nat :=
  if need p then some (result p) else none

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitness
