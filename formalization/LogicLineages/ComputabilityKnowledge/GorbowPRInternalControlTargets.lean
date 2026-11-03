module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalControlDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

def ActualEvaluation : Prop :=
  (∀ x : Nat, evaluate zeroTest (x ::ᵥ List.Vector.nil) = if x = 0 then 1 else 0) ∧
  (∀ x a b : Nat, evaluate conditional (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) =
    if x = 0 then a else b)

/-- The actual truth test used by checker formulas, in the exact call=1
orientation. No interpretation/evaluator hypothesis supplies the proof. -/
def InternalZeroTest : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨1, zeroTest⟩ →
  ∀ ctx (x : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (GorbowBooleanTruth.biconditional
      (.equal (GorbowPRDefiningEquations.call tag (x ::ᵥ List.Vector.nil)) (Term.numeral 1))
      (.equal x .zero)))

def InternalBooleanRange : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨1, zeroTest⟩ →
  ∀ ctx (x : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.disj (.equal (GorbowPRDefiningEquations.call tag (x ::ᵥ List.Vector.nil)) .zero)
      (.equal (GorbowPRDefiningEquations.call tag (x ::ᵥ List.Vector.nil)) (Term.numeral 1))))

/-- Full zero/nonzero branch laws for arbitrary symbolic control and outputs,
not merely numeral or already-Boolean controls. -/
def InternalConditional : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨3, conditional⟩ →
  ∀ ctx (x a b : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.conj
      (.imp (.equal x .zero)
        (.equal (GorbowPRDefiningEquations.call tag (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)) a))
      (.imp (.neg (.equal x .zero))
        (.equal (GorbowPRDefiningEquations.call tag (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil)) b))))

def Target : Prop := ActualEvaluation ∧ InternalZeroTest ∧ InternalBooleanRange ∧ InternalConditional

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.Targets
