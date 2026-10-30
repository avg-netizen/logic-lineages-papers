module

public import LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeTargets
open PredictionFiniteChange

def CandidateSpecification : Prop :=
  ∀ (R : Matrix) (z k t : Nat), candidate R z k t ≤ t + 1 ∧
    (candidate R z k t ≤ t → ∀ u : Nat, u ≤ t → R (z, k, candidate R z k t, u) = true) ∧
    ∀ s : Nat, s < candidate R z k t → s ≤ t → ∃ u : Nat, u ≤ t ∧ R (z, k, s, u) = false

def LeastWitnessStabilization : Prop :=
  ∀ (R : Matrix) (z k s : Nat), (∀ u : Nat, R (z, k, s, u) = true) →
    (∀ r : Nat, r < s → ¬ ∀ u : Nat, R (z, k, r, u) = true) →
      ∃ T : Nat, ∀ t : Nat, T ≤ t → candidate R z k t = s

def NoWitnessEscape : Prop :=
  ∀ (R : Matrix) (z k : Nat), (¬ ∃ s : Nat, ∀ u : Nat, R (z, k, s, u) = true) →
    ∀ b : Nat, ∃ T : Nat, ∀ t : Nat, T ≤ t → b < candidate R z k t

def FiniteChangesIffWitness : Prop :=
  ∀ (R : Matrix) (z k : Nat), (changeSet R z k).Finite ↔ ∃ s : Nat, ∀ u : Nat, R (z, k, s, u) = true

def FiniteChangeComputable : Prop :=
  ∀ R : Matrix, Computable R →
    Computable (fun q : Nat × Nat × Nat => candidate R q.1 q.2.1 q.2.2) ∧
    Computable (fun q : Nat × Nat × Nat => changeEvent R q.1 q.2.1 q.2.2)

def FiniteChangeCharacteristicProgram : Prop :=
  ∀ R : Matrix, Computable R → ∃ p : Nat.Partrec.Code, ∀ z k t : Nat,
    Nat.Partrec.Code.eval p (Nat.pair z (Nat.pair k t)) =
      Part.some (if changeEvent R z k t then 1 else 0)

def FreshStageEnumeration : Prop :=
  ∀ (R : Matrix) (z k : Nat), stageOutput R z k 0 = none ∧
    (∀ t a : Nat, stageOutput R z k t = some a ↔ a = t ∧ t ∈ changeSet R z k) ∧
    ∀ s t : Nat, s < t → stageOutput R z k s ≠ some t

def PiThreeFiniteChangeReduction : Prop :=
  ∀ (R : Matrix) (z : Nat),
    (∀ k : Nat, ∃ s : Nat, ∀ u : Nat, R (z, k, s, u) = true) ↔
      ∀ k : Nat, (changeSet R z k).Finite

end LogicLineages.ComputabilityKnowledge.PredictionFiniteChangeTargets
