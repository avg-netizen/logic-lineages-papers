module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection.Targets

/-- Exact least offset for EVERY original occurrence, all-x domain safety,
literal reconstruction, and equality/order preservation on original shifts. -/
def OriginalDomainAndRebasing : Prop := ∀ row : Row,
  (∀ d : Nat, domainOffset row ≤ d ↔
    ∀ a ∈ row, 0 ≤ (d : Int) + a.2) ∧
  (∀ a ∈ row, ∀ x : Nat,
    0 ≤ (x : Int) + (domainOffset row : Int) + a.2 ∧
    ((x + rebaseKey row a.2 : Nat) : Int) =
      (x : Int) + (domainOffset row : Int) + a.2 ∧
    originalShift row (rebaseKey row a.2) = a.2) ∧
  (∀ a ∈ row, ∀ b ∈ row,
    (rebaseKey row a.2 = rebaseKey row b.2 ↔ a.2 = b.2) ∧
    (rebaseKey row a.2 ≤ rebaseKey row b.2 ↔ a.2 ≤ b.2) ∧
    (rebaseKey row a.2 < rebaseKey row b.2 ↔ a.2 < b.2))

/-- Exact arbitrary-evaluator identities, literal signed block sums, complete
surviving support, zero cancellation, distinctness, and original mass bound.
The natural-evaluator identity is evaluated at the safe shift x + D. -/
def ExactCollectionAndSupport : Prop := ∀ row : Row,
  (∀ f : Int → Int,
    CommonHeadCollectedRow.weighted (fun k => f (originalShift row k))
      (collected row) = weighted f row) ∧
  (∀ (f : Nat → Int) (x : Nat),
    CommonHeadCollectedRow.weighted (fun k => f (x + k)) (collected row) =
      weighted (fun b => f (((x : Int) + (domainOffset row : Int) + b).toNat)) row) ∧
  (collected row).Pairwise (fun a b => a.2 ≠ b.2) ∧
  (∀ a ∈ collected row,
    a.1 ≠ 0 ∧ a.1 = coefficient row (originalShift row a.2) ∧
      ∃ b ∈ row, b.2 = originalShift row a.2 ∧ rebaseKey row b.2 = a.2) ∧
  (∀ b : Int, coefficient row b ≠ 0 ↔
    ∃ a ∈ collected row, originalShift row a.2 = b) ∧
  (collected row = [] ↔ ∀ b : Int, coefficient row b = 0) ∧
  CommonHeadLargeRow.mass (collected row) ≤ (row.map (fun a => a.1.natAbs)).sum

/-- B is the actual computed greatest surviving SIGNED shift, with its actual
nonzero block coefficient. Empty/all-cancelled rows have no leading claim. -/
def ActualGreatestSurvivingShift : Prop := ∀ row : Row, collected row ≠ [] →
  (leadingCoefficient row, greatestKey row) ∈ collected row ∧
  leadingCoefficient row ≠ 0 ∧
  (∀ a ∈ collected row, a.2 ≤ greatestKey row) ∧
  (∃ a ∈ row, a.2 = greatestShift row) ∧
  (∀ b : Int, coefficient row b ≠ 0 → b ≤ greatestShift row)

/-- Uniform primitive recursion of these very finite algorithms under the
standard integer/list coding. No effectiveness oracle or evaluator supplied. -/
def UniformPrimitiveRecursiveData : Prop :=
  Primrec domainOffset ∧
  Primrec₂ rebaseKey ∧
  Primrec₂ originalShift ∧
  Primrec rebaseRow ∧
  Primrec collected ∧
  Primrec₂ coefficient ∧
  Primrec greatestKey ∧
  Primrec greatestShift ∧
  Primrec leadingCoefficient

end LogicLineages.OrdinalComparison.SignedShiftCollection.Targets
