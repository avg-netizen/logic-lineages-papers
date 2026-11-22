module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowSliceValue
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open SignedRowCoordinateSlice (slice selected untouched)
open PreparedProjection

def valueAt (f ρ : Nat → Nat) (c : Int) (terms : List WeightedOperand) (result : Int) : Prop :=
  ∃ values : List Nat, orderedReads f ρ terms values ∧ c + actualSum terms values = result

/-- The same original ordered reads give exactly the selected and
untouched ordered lists. Their signed sums add to the original sum. -/
def SplitAndRejoin : Prop :=
  ∀ (f ρ : Nat → Nat) (rank : Nat) (terms : List WeightedOperand) (result : Int),
    (∃ values : List Nat, orderedReads f ρ terms values ∧ actualSum terms values = result) ↔
    ∃ taken kept : List Nat,
      orderedReads f ρ (selected rank terms) taken ∧ orderedReads f ρ (untouched rank terms) kept ∧
      actualSum (selected rank terms) taken + actualSum (untouched rank terms) kept = result

def ExactValueAtHit : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand)
      (b : Int) (residual : List WeightedOperand),
    ρ rank = a → slice f rank a c terms = some (some (b,residual)) →
    ∀ result : Int, valueAt f ρ c terms result ↔ valueAt f ρ b residual result

/-- Original signed equality, weak inequality and strict inequality on
the actual reads of the same source row and its true residual. -/
def ComparisonsAtHit : Prop :=
  ∀ (f ρ : Nat → Nat) (rank a : Nat) (c : Int) (terms : List WeightedOperand)
      (b : Int) (residual : List WeightedOperand),
    ρ rank = a → slice f rank a c terms = some (some (b,residual)) →
    (valueAt f ρ c terms 0 ↔ valueAt f ρ b residual 0) ∧
    ((∃ value : Int, valueAt f ρ c terms value ∧ 0 ≤ value) ↔
      ∃ value : Int, valueAt f ρ b residual value ∧ 0 ≤ value) ∧
    ((∃ value : Int, valueAt f ρ c terms value ∧ 0 < value) ↔
      ∃ value : Int, valueAt f ρ b residual value ∧ 0 < value)

def FullSignedRowSliceValue : Prop := SplitAndRejoin ∧ ExactValueAtHit ∧ ComparisonsAtHit

end LogicLineages.PermittedControl.SignedRowSliceValue
