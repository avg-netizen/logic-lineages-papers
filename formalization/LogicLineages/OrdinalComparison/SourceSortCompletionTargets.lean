module
public import LogicLineages.OrdinalComparison.SourceSortCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSortCompletion.Targets

/-- Whole paper09 lem:sort: actual full source S graph calibration, pair coding
as multiset equality, and the displayed primitive-positive sorting graph.
No correctness premise for the source evaluator, no independently valued
copies of a shared name, and no all-ground decision claim. -/
def FullSourceSort : Prop :=
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (x : Variable Γ .ground) (y : Nat),
    Observation ρ (successorProbe x) y ↔ y = Phi (input ρ x + 4)) ∧
  (∀ a b c d : Nat,
    successorObservation a + successorObservation b = successorObservation c + successorObservation d ↔
    ({a, b} : Multiset Nat) = {c, d}) ∧
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (a b low high : Variable Γ .ground) (difference : Nat),
    SortFormula ρ a b low high difference ↔
      input ρ low = min (input ρ a) (input ρ b) ∧
      input ρ high = max (input ρ a) (input ρ b) ∧
      difference = max (input ρ a) (input ρ b) - min (input ρ a) (input ρ b))
end LogicLineages.OrdinalComparison.Source.SourceSortCompletion.Targets
