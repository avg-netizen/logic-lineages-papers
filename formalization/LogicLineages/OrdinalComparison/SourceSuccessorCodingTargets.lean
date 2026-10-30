module

public import LogicLineages.OrdinalComparison.SourceSuccessorCodingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def SuccessorProbeDenotation : Prop :=
  ∀ (Γ : List Ty) (x : Variable Γ .ground) (ρ : OrdinalComponent Γ → Ordinal.{0}) (n : Nat)
    (v : OrdinalVector Γ 0),
    ρ ⟨.ground, x, 0⟩ = ((n + 1 : Nat) : Ordinal) →
    ordinalApplicativeAssignment (successorProbe x) = some v →
      denote ρ (v 0) = (successorRaw n : Ordinal)

def SuccessorObservationCalibration : Prop :=
  ∀ n : Nat, successorRaw n = Phi (n + 4) + 1 ∧ successorObservation n = Phi (n + 4)

def SuccessorObservationGrowth : Prop :=
  (∀ n : Nat, 0 < successorObservation n) ∧ StrictMono successorObservation ∧
    ∀ n : Nat, 2 * successorObservation n < successorObservation (n + 1)

def SuccessorPairCoding : Prop :=
  ∀ a b c d : Nat,
    successorObservation a + successorObservation b = successorObservation c + successorObservation d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def SuccessorSortedWitness : Prop :=
  ∀ a b low high difference : Nat,
    (successorObservation a + successorObservation b = successorObservation low + successorObservation high ∧
      low + difference = high) ↔
    low = min a b ∧ high = max a b ∧ difference = max a b - min a b

end LogicLineages.OrdinalComparison.Source.Targets
