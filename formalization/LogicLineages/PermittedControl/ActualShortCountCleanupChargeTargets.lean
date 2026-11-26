module
public import LogicLineages.PermittedControl.ActualShortCountCleanupTargets
public import LogicLineages.PermittedControl.ActualZeroClassOutputStateTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualShortCountCleanupCharge
open scoped Classical
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets
open ActualZeroClassOutputState ActualShortCountCleanup

/-- Order-preserving deletion is constant on each operand key. Identical
keys, including signed cancellation of repeated occurrences, cannot
be split across the filter. -/
def ExactCleanupGroupedCoefficients : Prop :=
  ∀ (before : List Read) (op : LowerOperand),
    groupedWeights (retained before) op =
      if shortLength op = 0 then groupedWeights before op else 0

/-- Structural charge comparison needs no actual guard: it follows
from exactly which signed coefficients were retained. -/
def ExactCleanupCharge : Prop :=
  ∀ (r : Nat) (constant : Int) (before : List Read),
    let src := rankedRow r constant before
    let out := rankedRow r (constant + shortShift before) (retained before)
    out.value = src.value ∧
    out.count = src.count.filter (fun k => shortLength (countOperand r k) = 0) ∧
    out.count.support ⊆ src.count.support ∧
    countCharge out ≤ countCharge src ∧ valueCount out = valueCount src

/-- The second structural transition is cleanup of the previous output,
not a second zero-class replacement. -/
def CleanedOutput (f ρ : Nat → Nat) (r : Nat) (constant : Int) (raw : List Read)
    (installed : Int) (before : List Read) : Prop :=
  let after := retained before
  let cleanConstant := installed + shortShift before
  let src := rankedRow r constant raw
  let mid := rankedRow r installed before
  let out := rankedRow r cleanConstant after
  after.Sublist before ∧ liftedReads f ρ after ∧
  (∀ rd ∈ after, LongCountOperand rd.1.2) ∧ OriginalRanks raw after ∧
  (∀ rd ∈ after, rd.1.2.rank < r) ∧
  constant + readSum raw = cleanConstant + readSum after ∧
  out.value = mid.value ∧
  out.count = mid.count.filter (fun k => shortLength (countOperand r k) = 0) ∧
  countCharge out ≤ countCharge src ∧ valueCount out ≤ valueCount src ∧
  countCharge out + valueCount out < countCharge src + valueCount src

/-- Original zero-step witness and its exactly cleaned actual output.
Only long count shape is furnished, not the next annotation norm tail. -/
def ExactConcreteLongOutputState : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (C r : Nat) (constant : Int) (raw xs : List Read) (annotations : List Annotation),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    Ready f B ρ C (xs.map Prod.fst) annotations →
    C ∈ fullValues f annotations →
    (rowParts f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).1 = 0 →
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    let ps := cohort f C terms annotations
    TransferReady B ρ ps →
    let anchor := leastPrefix ps
    ∃ (moved : List Read) (ledger : List DispositionEntry) (x₀ : Fin r)
      (q : NONote × NONote),
      MovedAt f ρ anchor ps moved ∧ liftedReads f ρ moved ∧ AnchorAt anchor x₀ q ∧
      DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved ∧
      ConcreteEquations f C r constant raw xs annotations x₀ q ledger moved ∧
      let after := outsideCohort f C terms values annotations ++ moved
      let installed := constant + (replaceRow f C terms values annotations).2
      let src := rankedRow r constant raw
      let out := rankedRow r installed after
      liftedReads f ρ after ∧ OriginalRanks raw after ∧
      (∀ rd ∈ after, rd.1.2.rank < r) ∧
      constant + readSum raw = installed + readSum after ∧
      out = concreteRow f C r constant xs annotations moved ∧
      ZeroClassReplacement src out ∧
      countCharge out ≤ countCharge src ∧ valueCount out ≤ valueCount src ∧
      countCharge out + valueCount out < countCharge src + valueCount src ∧
      CleanedOutput f ρ r constant raw installed after

def FullActualShortCountCleanupCharge : Prop :=
  ExactCleanupGroupedCoefficients ∧ ExactCleanupCharge ∧ ExactConcreteLongOutputState

end LogicLineages.PermittedControl.ActualShortCountCleanupCharge
