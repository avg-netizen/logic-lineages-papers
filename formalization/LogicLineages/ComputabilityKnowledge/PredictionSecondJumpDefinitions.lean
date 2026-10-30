module

public import LogicLineages.ComputabilityKnowledge.OraclePiTwoDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionRelativeSelectionDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionMaximumDefinitions

@[expose] public section
/-! Paper14 lem:list assembly uses the actual twice-iterated checked halting
jump, not the former semantic totality/equality oracles. Canonical entry n
is source a_(n+1); canonicalPrefix m contains exactly source entries 1..m.
The ordinary compiled bound evaluates without any oracle. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionSecondJump
open OracleJump PredictionCanonicalList PredictionMaximum

noncomputable def secondJumpOracles : Set (Nat → Part Nat) := {fun n => Part.some (secondJump n)}

noncomputable def compiledBoundIndex (universal : Nat.Partrec.Code) (m : Nat) : Nat :=
  Encodable.encode (compileMaximum universal (canonicalPrefix m))

end LogicLineages.ComputabilityKnowledge.PredictionSecondJump
