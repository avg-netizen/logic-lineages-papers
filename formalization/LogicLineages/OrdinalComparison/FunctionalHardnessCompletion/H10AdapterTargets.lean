module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ReductionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Targets
open LogicLineages.ComputabilityKnowledge
open PolynomialCircuit PolynomialDomainShift CircuitLinear
open PositiveExpression

def ImpossibleSystemCorrect : Prop := WellFormedCode impossibleSystem ∧
  ¬ encodedPolynomialSolvable impossibleCode

def OriginalSafety : Prop := ∀ xs : List Nat,
  H10Validity.validInput xs=false → translate xs=impossibleCode

/-- Arbitrary parseable valid lists, not merely re-encoded canonical lists. -/
def ParsedCalibration : Prop := ∀ (xs : List Nat) (p : PolynomialCircuit.Code),
  PolynomialCircuit.decode xs=some p → p.WellFormed →
  translate xs=Encodable.encode (encodeCircuitSystem (PolynomialCircuit.compile (shift p)))

def ReductionPrimitive : Prop := Primrec reduce

def PolynomialCircuitRoot : Prop := ∀ p : PolynomialCircuit.Code, p.WellFormed →
  (HasNonnegativeRoot p ↔
    ∃ ρ : Nat → PosNat, (PolynomialCircuit.compile (shift p)).outputEqual ρ)

/-- Exact original bridge contract remains separate from these supporting
facts until the literal full-circuit semantic theorem is proved. -/
abbrev CodedH10ToLinearSystems : Prop := H10ReductionTargets.CodedH10ToLinearSystems

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.Targets
