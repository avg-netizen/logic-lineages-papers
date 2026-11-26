module
public import LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumnsTargets
public import LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionAdmissibilityTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
open scoped Classical
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualRankedZeroClass
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys
open ActualZeroClassSelectedDispositionSums InnerTerminationTargets

/-- The actual ranked output: untouched outside reads, actual moved reads,
and the signed correction installed by original replaceRow. -/
noncomputable def concreteRow (f : Nat → Nat) (C r : Nat) (constant : Int) (xs : List Read)
    (annotations : List Annotation) (moved : List Read) : RankedRow r :=
  rankedRow r (constant + (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2)
    (outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations ++ moved)

/-- Expose the exact original class, criterion and witnessed finite
replacement columns, not just the abstract existential relation. -/
def ConcreteEquations (f : Nat → Nat) (C r : Nat) (constant : Int) (raw xs : List Read)
    (annotations : List Annotation) (x₀ : Fin r) (q : NONote × NONote)
    (ledger : List DispositionEntry) (moved : List Read) : Prop :=
  let row := rankedRow r constant raw
  let out := concreteRow f C r constant xs annotations moved
  let chosen := finiteClassColumns r (classReads f C xs annotations)
  let d := dispositionAt (keyedLedger r ledger)
  chosen.1 ⊆ row.value.support ∧ chosen.2 ⊆ row.count.support ∧
  (chosen.1.Nonempty ∨ chosen.2.Nonempty) ∧
  (2 * (∑ k ∈ chosen.1, row.value k) + (∑ k ∈ chosen.2, row.count k) = 0) ∧
  (∀ k ∈ chosen.2, (d k).Admissible x₀ k.2) ∧
  (out.value = row.value.filter (· ∉ chosen.1)) ∧
  (out.count = row.count.filter (· ∉ chosen.2) +
    (∑ k ∈ chosen.2, (d k).term x₀ q (row.count k))) ∧
  (out.const = row.const + (∑ k ∈ chosen.2, row.count k * (d k).shift))

/-- Construct the actual structural replacement witness for one original
selected zero class. For an absent survivor only, obtain a dummy Fin r
from the actual nonempty finite class; r=0 cannot enter this branch. -/
def ExactConcreteZeroClassAssembly : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (C r : Nat) (constant : Int) (raw xs : List Read) (annotations : List Annotation),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    Ready f B ρ C (xs.map Prod.fst) annotations →
    C ∈ fullValues f annotations →
    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 = 0 →
    let ps := cohort f C (xs.map Prod.fst) annotations
    TransferReady B ρ ps →
    let anchor := leastPrefix ps
    ∃ (moved : List Read) (ledger : List DispositionEntry) (x₀ : Fin r)
      (q : NONote × NONote),
      MovedAt f ρ anchor ps moved ∧ liftedReads f ρ moved ∧ AnchorAt anchor x₀ q ∧
      DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved ∧
      ConcreteEquations f C r constant raw xs annotations x₀ q ledger moved ∧
      ZeroClassReplacement (rankedRow r constant raw)
        (concreteRow f C r constant xs annotations moved)

end LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
