module
public import Mathlib.Data.Finset.Sort

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCoordinateRankChart

def cells (θ : Nat → Nat) (names : List Nat) : Finset Nat := (names.map θ).toFinset

abbrev size (θ : Nat → Nat) (names : List Nat) : Nat := (cells θ names).card

noncomputable def ordered (θ : Nat → Nat) (names : List Nat) :
    Fin (size θ names) ≃o cells θ names :=
  (cells θ names).orderIsoOfFin rfl

/-- Canonical rank of an observed value. A name outside the given list is
under no constraint from the chart, even if its value has a matching cell. -/
noncomputable def rankOf (θ : Nat → Nat) (names : List Nat) (name : Nat) : Nat :=
  if h : θ name ∈ cells θ names then
    ((ordered θ names).symm ⟨θ name,h⟩).val
  else 0

/-- Real observed values on the finite initial segment. The strictly
increasing ambient extension is used only to match the charge API. -/
noncomputable def rankValue (θ : Nat → Nat) (names : List Nat) (rank : Nat) : Nat :=
  if h : rank < size θ names then
    (ordered θ names ⟨rank,h⟩).val
  else (cells θ names).sup id + rank + 1

def ExactDenseRankChart : Prop :=
  ∀ (θ : Nat → Nat) (names : List Nat),
    StrictMono (rankValue θ names) ∧
    (∀ name ∈ names,
      rankOf θ names name < size θ names ∧ rankValue θ names (rankOf θ names name) = θ name) ∧
    (∀ k : Nat, k < size θ names → ∃ name ∈ names, rankOf θ names name = k) ∧
    ∀ i ∈ names, ∀ j ∈ names,
      (rankOf θ names i = rankOf θ names j ↔ θ i = θ j) ∧
      (rankOf θ names i < rankOf θ names j ↔ θ i < θ j)

end LogicLineages.PermittedControl.ActualCoordinateRankChart
