module
public import LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingTargets
open PredictionAlphabetEmbedding

def EffectiveEmbedding : Prop := Primrec liftCode

def ExactStepEmbedding : Prop :=
  ∀ (p : PredictionTapeTable.Table) (c : PredictionTapeTable.Raw),
    PredictionFiniteAlphabet.step (liftTable p) (liftRaw c) =
      (PredictionTapeTable.step p c).map liftRaw

def ExactSimulationEmbedding : Prop :=
  ∀ (code fuel : Nat) (xs : List Bool),
    PredictionFiniteAlphabet.simulate (liftCode code) fuel xs =
      (PredictionTapeTable.simulate code fuel xs).map liftRaw

/-- The already-proved constant-time evaders retain exactly the same fuel
threshold, not merely termination under the larger work-alphabet model. -/
def ExactEvaderRuntime : Prop :=
  ∀ (k : Nat) (xs : List Bool) (fuel : Nat),
    (∃ d : PredictionFiniteAlphabet.Raw,
      PredictionFiniteAlphabet.simulate (liftCode (PredictionTapeCode.code k)) fuel xs = some d) ↔
      min k xs.length + 2 ≤ fuel

def ExactEvaderOutput : Prop :=
  ∀ (k : Nat) (xs : List Bool) (fuel : Nat) (d : PredictionFiniteAlphabet.Raw),
    PredictionFiniteAlphabet.simulate (liftCode (PredictionTapeCode.code k)) fuel xs = some d →
      d.2.1 = (if xs.length < k then 2 else 1)

end LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingTargets
