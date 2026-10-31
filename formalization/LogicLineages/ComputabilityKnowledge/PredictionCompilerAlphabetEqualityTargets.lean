module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityTargets
open PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality

def CompleteWorkAlphabet : Prop := ∀ a : TapeAlphabet, a ∈ workSymbols

def ExactWorkSymbolComparison : Prop := ∀ a b : TapeAlphabet, workEq a b = true ↔ a = b

def ExactInputFunctionComparison : Prop :=
  ∀ (β : Type) (compare : β → β → Bool),
    (∀ x y : β, compare x y = true ↔ x = y) →
    ∀ f g : TapeAlphabet → Store → β, sameInputs compare f g = true ↔ f = g

end LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityTargets
