module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutTargets
open Turing Turing.PartrecToTM2 PredictionBinarySentinel PredictionBinaryParameterLayout

def BitsPrimitiveRecursive : Prop := Primrec bits

def ExactNaturalBits : Prop := ∀ n : Nat, (bits n).map bitSymbol = trNat n

def ExactParameterLayout : Prop :=
  ∀ (e : Nat) (xs : List Bool),
    PredictionCompilerFiniteExecution.sourceInput [inputNat xs, e] = parameterWord e ++ xs.map rawSymbol

def NumericWordPrimitiveRecursive : Prop := Primrec numericWord

def ExactNumericWord : Prop := ∀ e : Nat, (parameterWord e).map symbolIndex = numericWord e

end LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutTargets
