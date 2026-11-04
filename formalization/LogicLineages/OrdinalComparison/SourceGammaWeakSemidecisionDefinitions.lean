module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCounterexampleDefinitions
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision
noncomputable def test (b code k : Nat) : Bool :=
  match Encodable.decode (α := List Nat) k with
  | none => false
  | some xs => SourceGammaWeakCounterexample.counterexample b code xs
noncomputable def search (b code : Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (test b code k))
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision
