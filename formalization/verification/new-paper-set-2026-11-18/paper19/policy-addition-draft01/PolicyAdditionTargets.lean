module
public import LogicLineages.ControlSensitivityCurrent.PolicyAdditionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyAdditionTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion PolicyAddition

def ExactAddition : Prop := ∀ p : AdmissibleSum.Policy, ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat, n ≤ G n) →
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b c : Variable Γ .ground),
    (∀ d : Nat, PolicyAddition.AddWitness p G ρ a b c d ↔
      input ρ a + input ρ b = input ρ c ∧ d = 3 * input ρ b) ∧
    (PolicyAddition.AddFormula p G ρ a b c ↔ input ρ a + input ρ b = input ρ c)

def ExactOne : Prop := ∀ p : AdmissibleSum.Policy, ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat, n ≤ G n) → ∀ u : Nat,
    PolicyAddition.OneFormula p G u ↔ u = 1

def ExactBinaryDAG : Prop := ∀ p : AdmissibleSum.Policy, ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat, n ≤ G n) → ∀ k : Nat,
    (binaryDAG k).gates ≤ 2 * (Nat.log2 k + 1) ∧
    ∀ y : Nat, PolicyAddition.Run p G (binaryDAG k) y ↔ y = k
end LogicLineages.ControlSensitivityCurrent.PolicyAdditionTargets
