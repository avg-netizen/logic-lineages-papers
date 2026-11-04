module
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleDefinitions
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision
noncomputable def test (b code k : Nat) : Bool :=
  match Encodable.decode (α := List Nat) k with
  | none => false
  | some xs => SourceGammaCounterexample.counterexample b code xs
noncomputable def search (b code : Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (test b code k))
end LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision
