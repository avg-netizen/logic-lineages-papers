module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitLinearDefinitions
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Targets
open LogicLineages.ComputabilityKnowledge.CircuitReduction
open LogicLineages.ComputabilityKnowledge.PositiveExpression

def FullCircuitEncoding : Prop := ∀ c : Circuit, c.WellFormed →
  WellFormedCode (encodeCircuitSystem c) ∧
    ((∃ ρ : Nat → PosNat, c.outputEqual ρ) ↔
      PolynomialSatisfiable (systemOfCode (encodeCircuitSystem c)))

/-- Effectivity acts on the existing actual finite circuit codec, and returns
the actual Encodable natural code of the linear polynomial system. It does
not assume a computable encoder on an abstract polynomial quotient. -/
def NumericCircuitEncoder : Prop :=
  ∃ encode : List Nat → Option Nat, Primrec encode ∧ ∀ c : Circuit,
    encode (encodeCircuit c) = some (Encodable.encode (encodeCircuitSystem c))

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Targets
