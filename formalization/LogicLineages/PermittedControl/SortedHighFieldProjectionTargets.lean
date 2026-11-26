module
public import LogicLineages.PermittedControl.StableSortedHighFieldTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StableSortedHighField
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

def projection (F G : ValueField) (lowRank wanted : Nat) : NormalForm.Formula :=
  eliminatePreparedFormula (guardedPacket F G lowRank wanted).2

def ActualSortedHighProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (F G : ValueField), ProperField F → ProperField G →
  ∀ (ρ : Nat → Nat) (lowRank highRank wanted : Nat), lowRank < highRank →
    highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ ρ lowRank →
    let table := (guardedPacket F G lowRank wanted).1
    let output := projection F G lowRank wanted
    PreparedInput table output ∧ 0 ∉ output.variables ∧
    (∃ ν : Nat → Nat, PreparedTableTied f highRank ρ table ν ∧
      ∀ (j : Nat) (used : j < table.length),
        lowerOperandRead f ρ (table.get ⟨j,used⟩) = some (some (ν (j+1)))) ∧
    (∀ ν : Nat → Nat, PreparedTableTied f highRank ρ table ν →
      (output.eval ν ↔ ∃ z : Nat, ρ lowRank < z ∧ actualOutcome f F G (ρ lowRank) z wanted))

end LogicLineages.PermittedControl.StableSortedHighField
