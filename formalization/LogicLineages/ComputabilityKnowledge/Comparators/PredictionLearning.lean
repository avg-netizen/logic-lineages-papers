module

public import LogicLineages.ComputabilityKnowledge.PredictionLearning

@[expose] public section

/-! Independently fixed target for paper14 lem:learning (lines169–182).
The source Learns predicate is actual eventual agreement in the simultaneous
finite-history game, not defined as absence of certificates. The Boolean
matrix has an actual Mathlib Computable certificate, not classical Decidable.
This does not assert the runtime bound, threshold hardness, or oracle degree.
Written by Codex before Claude proof authorship. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.PredictionLearning

open LogicLineages.ComputabilityKnowledge.PredictionLearning
open LogicLineages.ComputabilityKnowledge.PredictionGame

def ErrorCertificateSound : Prop :=
  ∀ (p e : Code) (hp : TotalBinary p) (he : TotalBinary e) (fuel n : Nat),
    boundedError p e fuel n = some true →
    prediction (policy p hp) (policy e he) n ≠
      evasion (policy p hp) (policy e he) n

def ErrorCertificateComplete : Prop :=
  ∀ (p e : Code) (hp : TotalBinary p) (he : TotalBinary e) (n : Nat),
    prediction (policy p hp) (policy e he) n ≠
      evasion (policy p hp) (policy e he) n →
    ∃ fuel : Nat, boundedError p e fuel n = some true

def RecursiveMatrix : Prop :=
  Computable (fun x : Code × Code × Nat × Nat =>
    learningMatrix x.1 x.2.1 x.2.2.1 x.2.2.2)

def LearningFormula : Prop :=
  ∀ (p e : Code) (hp : TotalBinary p) (he : TotalBinary e),
    Learns (policy p hp) (policy e he) ↔
      ∃ cutoff : Nat, ∀ certificate : Nat,
        learningMatrix p e cutoff certificate = true

def Target : Prop :=
  ErrorCertificateSound ∧ ErrorCertificateComplete ∧ RecursiveMatrix ∧ LearningFormula

end LogicLineages.ComputabilityKnowledge.Comparators.PredictionLearning
