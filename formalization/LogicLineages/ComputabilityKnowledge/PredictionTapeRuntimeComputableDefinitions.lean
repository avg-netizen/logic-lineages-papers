module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputable

def allHalting (code n fuel : Nat) : Bool :=
  (PredictionCommonFuel.booleanHistories n).all
    (fun xs => (PredictionFiniteAlphabet.simulate code fuel xs).isSome)

def partialWorstTime (code n : Nat) : Part Nat :=
  Nat.rfind (fun fuel => Part.some (allHalting code n fuel))

end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputable
