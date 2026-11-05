module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitNumericDefinitions
public import LogicLineages.ComputabilityKnowledge.PolynomialDomainShift
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter
open LogicLineages.ComputabilityKnowledge

/-- A well-formed system with no unknowns and the impossible constant equation
1=0. Malformed original inputs are sent here, not silently repaired. -/
def impossibleSystem : SystemCode := (0, [[(1,0,none)]])
def impossibleCode : Nat := Encodable.encode impossibleSystem

/-- Validate ORIGINAL references before any new circuit wire is allocated.
Only then shift the zero-allowing domain and compile the literal circuit. -/
def translate (xs : List Nat) : Nat :=
  if H10Validity.validInput xs then
    ((PolynomialDomainShift.encodedShift xs).bind fun shifted =>
      (PolynomialCircuit.compileCode shifted).bind CircuitNumeric.encode).getD impossibleCode
  else impossibleCode

/-- Total standard-natural-code reduction, including outer decode failure. -/
def reduce (e : Nat) : Nat :=
  ((Encodable.decode e : Option (List Nat)).map translate).getD impossibleCode

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter
