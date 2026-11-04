module
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerDefinitions
public import Mathlib.Computability.PartrecCode
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceBlankHaltingReduction
open Turing LogicLineages.ComputabilityKnowledge
open PredictionFiniteAlphabet

/-- Ignore the supplied input, run c on zero, and return zero only after it halts. -/
def normalize (c : Nat.Partrec.Code) : Nat.Partrec.Code :=
  .comp .zero (.comp c .zero)
def normalizedIndex (e : Nat) : Nat :=
  Encodable.encode (normalize (Nat.Partrec.Code.ofNatCode e))
def translate (U : Turing.ToPartrec.Code) (e : Nat) : Nat :=
  PredictionUniformBinaryCompiler.compile U (normalizedIndex e)
def machineEval (code : Nat) (xs : List Bool) :
    Part (TM0.Cfg (Fin (width (decodeTable code))) Nat) :=
  StateTransition.eval (TM0.step (machine (decodeTable code)))
    (toCfg (decodeTable code) (initial (decodeTable code) xs))
end LogicLineages.OrdinalComparison.SourceBlankHaltingReduction
