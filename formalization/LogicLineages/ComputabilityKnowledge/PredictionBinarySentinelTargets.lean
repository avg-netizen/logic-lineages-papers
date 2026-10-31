module
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelTargets
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionBinarySentinel

def EffectiveSentinel : Prop := Primrec inputNat

def ExactNaturalEncoding : Prop :=
  ∀ xs : List Bool, trNat (inputNat xs) = (xs.map bitSymbol).reverse ++ [Γ'.bit1]

def ExactInputLayout : Prop :=
  ∀ xs : List Bool, PredictionCompilerFiniteExecution.sourceInput [inputNat xs] =
    bottomSymbol :: rawSymbol true :: xs.map rawSymbol

def InjectiveSentinel : Prop := Function.Injective inputNat

def ExactBinarySlots : Prop :=
  rawIndex false = 1 ∧ rawIndex true = 2 ∧
    (rawSymbol false ≠ (default : TapeAlphabet)) ∧
    (rawSymbol true ≠ (default : TapeAlphabet)) ∧ rawSymbol false ≠ rawSymbol true

end LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelTargets
