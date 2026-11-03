module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmeticDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

def ActualEvaluation : Prop :=
  (∀ x y : Nat, evaluate addition (y ::ᵥ x ::ᵥ List.Vector.nil) = x + y) ∧
  (∀ x y : Nat, evaluate multiplication (y ::ᵥ x ::ᵥ List.Vector.nil) = x * y) ∧
  (∀ a b : Nat, evaluate pairing (a ::ᵥ b ::ᵥ List.Vector.nil) = GorbowRegistryTuple.pair a b)

/-- Actual finite Hilbert proof, arbitrary variable-containing arguments. -/
def InternalAddition : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨2, addition⟩ →
  ∀ ctx (x y : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call tag (y ::ᵥ x ::ᵥ List.Vector.nil)) (.add x y)))

def InternalMultiplication : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨2, multiplication⟩ →
  ∀ ctx (x y : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call tag (y ::ᵥ x ::ᵥ List.Vector.nil)) (.mul x y)))

def InternalPairing : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨2, pairing⟩ →
  ∀ ctx (a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call tag (a ::ᵥ b ::ᵥ List.Vector.nil))
      (GorbowRegistryTuple.pairTerm a b)))

def Target : Prop := ActualEvaluation ∧ InternalAddition ∧ InternalMultiplication ∧ InternalPairing

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic.Targets
