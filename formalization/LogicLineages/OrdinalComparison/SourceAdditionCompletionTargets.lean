module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Targets
open SourceSortCompletion

/-- Entire paper09 lem:addition: actual source equations with one fresh raw
positive witness, the constant-size source definition of one, and the
explicit binary doubling/add-one DAG with logarithmically many gates. -/
def FullSourceAddition : Prop :=
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat),
    AddWitness ρ a b c d ↔
      input ρ a + input ρ b = input ρ c ∧ d = 3 * input ρ b) ∧
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground),
    AddFormula ρ a b c ↔ input ρ a + input ρ b = input ρ c) ∧
  (∀ u : Nat, OneFormula u ↔ u = 1) ∧
  (∀ k : Nat, (binaryDAG k).gates ≤ 2 * (Nat.log2 k + 1) ∧
    ∀ y : Nat, (binaryDAG k).Run y ↔ y = k)
end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Targets
