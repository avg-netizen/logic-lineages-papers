module
public import LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumnsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTape
open scoped Classical
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualRankedZeroClass
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow ActualZeroClassOutsideAndShift

/-- The legitimate ordered views of one actual normalized source. The
order is not fixed by the original Finsupp listing. Cancellations are
permitted only after all actual original reads succeeded. -/
structure NormalizedTape (f ρ : Nat → Nat) (raw xs : List Read) : Prop where
  sourceReads : liftedReads f ρ raw
  outputReads : liftedReads f ρ xs
  unique : (originalKeys xs).Nodup
  covers : ∀ key : LowerOperand, key ∈ originalKeys xs ↔ key ∈ (groupedWeights raw).support
  sameValue : readSum raw = readSum xs
  records : ∀ rd ∈ xs, rd.1.1 = groupedWeights raw rd.1.2 ∧ rd.1.1 ≠ 0 ∧
    ∃ prior ∈ raw, prior.1.2 = rd.1.2 ∧ prior.2 = rd.2

def ExactLegacyTape : Prop :=
  ∀ (f ρ : Nat → Nat) (raw xs : List Read), liftedReads f ρ raw →
    normalizeReads f ρ raw = some xs → NormalizedTape f ρ raw xs

def ExactTapeWeights : Prop :=
  ∀ (f ρ : Nat → Nat) (raw xs : List Read), NormalizedTape f ρ raw xs →
    groupedWeights xs = groupedWeights raw

def ExactTapeRankedMembers : Prop :=
  ∀ (f ρ : Nat → Nat) (raw xs : List Read) (r : Nat) (c : Int),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
    ∀ rd ∈ xs, IsInRankedColumn (rankedRow r c raw) rd

def ExactTapeOutside : Prop :=
  ∀ (f ρ : Nat → Nat) (C : Nat) (raw xs : List Read) (anns : List Annotation),
    NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) anns →
      outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) anns =
        removeSelectedKeys (originalKeys (classReads f C xs anns)) xs

def ExactTapeRankedClass : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (r : Nat) (c : Int)
    (raw xs : List Read) (annotations : List Annotation) (C : Nat),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let row := rankedRow r c raw
    let selected := classReads f C xs annotations
    let columns := finiteClassColumns r selected
    columns.1 ⊆ row.value.support ∧ columns.2 ⊆ row.count.support ∧
    (columns.1.Nonempty ∨ columns.2.Nonempty) ∧
    (∀ k : ValueKey r, k ∈ columns.1 ↔ ∃ rd ∈ selected, rd.1.2 = valueOperand r k) ∧
    (∀ k : CountKey r, k ∈ columns.2 ↔ ∃ rd ∈ selected, rd.1.2 = countOperand r k) ∧
    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 =
      2 * (∑ k ∈ columns.1, row.value k) + ∑ k ∈ columns.2, row.count k

def ExactTapeOutsideRankedColumns : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let row := rankedRow r constant raw
    let chosen := finiteClassColumns r (classReads f C xs annotations)
    let outside := rankedRow r 0 (outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations)
    (outside.value = row.value.filter (fun k => k ∉ chosen.1)) ∧
    (outside.count = row.count.filter (fun k => k ∉ chosen.2))

def FullActualNormalizedTape : Prop :=
  ExactLegacyTape ∧ ExactTapeWeights ∧ ExactTapeRankedMembers ∧
  ExactTapeRankedClass ∧ ExactTapeOutside ∧ ExactTapeOutsideRankedColumns

end LogicLineages.PermittedControl.ActualNormalizedTape
