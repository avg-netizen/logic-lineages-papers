module
public import LogicLineages.ComputabilityKnowledge.PredictionSentinelDecodeProof
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.TuringMachine.Config
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFixedUniversal

/-- The existing ordinary partial evaluator, after exact sentinel input conversion.
No binary-output or totality restriction is imposed. -/
def run (n e : Nat) : Part Nat :=
  (Nat.Partrec.Code.ofNatCode e).eval (PredictionSentinelDecode.ordinaryInputCode n)

def vectorRun (v : List.Vector Nat 2) : Part Nat := run v.head v.tail.head
end LogicLineages.ComputabilityKnowledge.PredictionFixedUniversal
