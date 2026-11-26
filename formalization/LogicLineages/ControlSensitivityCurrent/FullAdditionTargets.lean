module
public import LogicLineages.ControlSensitivityCurrent.PolicyAdditionTargets
public import LogicLineages.ControlSensitivityCurrent.BinaryGeneratorTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullAddition.Targets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion
/-- Literal source growth conditions sufficient for these finite gadgets.
Omitting PR/upper-bound restrictions strengthens the mathematical claim. -/
def SourceGrowth (f : Nat → Nat) : Prop :=
  (∀ n : Nat, Phi n ≤ f n) ∧ (∀ n : Nat, 2 ^ (2 ^ f n) ≤ f (n+1))

/-- Complete current19 lem:addition, including an effective code for its DAG. -/
def CompleteAddition : Prop :=
  BinaryGeneratorTargets.ExactTerminalTrace ∧
  BinaryGeneratorTargets.ExactReconstruction ∧
  BinaryGeneratorTargets.UniformPrimitiveRecursive ∧
  ∀ f : Nat → Nat, SourceGrowth f →
    StrictMono f ∧ (∀ n : Nat, n < f n) ∧
    ∀ p : AdmissibleSum.Policy,
      (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b c : Variable Γ .ground),
        (∀ d : Nat, PolicyAddition.AddWitness p f ρ a b c d ↔
          input ρ a + input ρ b = input ρ c ∧ d = 3 * input ρ b) ∧
        (PolicyAddition.AddFormula p f ρ a b c ↔ input ρ a + input ρ b = input ρ c)) ∧
      (∀ u : Nat, PolicyAddition.OneFormula p f u ↔ u = 1) ∧
      (∀ k : Nat, (binaryDAG k).gates ≤ 2 * (Nat.log2 k + 1) ∧
        ∀ y : Nat, PolicyAddition.Run p f (binaryDAG k) y ↔ y = k)
end LogicLineages.ControlSensitivityCurrent.FullAddition.Targets
