module
public import LogicLineages.PermittedControl.ActualNormalizedTapeDispositionTargets
public import LogicLineages.PermittedControl.ActualShortCountCleanupChargeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransition
open scoped Classical
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualRankedRowColumns ActualZeroClassCohortTransfer ActualRankedZeroClass
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets
open ActualZeroClassOutputState ActualShortCountCleanupCharge ActualNormalizedTape

/-- Assemble the actual ordered transition for its own least surviving
prefix, retaining original source readiness and true transfer domain. -/
def ExactTapeZeroAssembly : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (C r : Nat) (constant : Int) (raw xs : List Read) (annotations : List Annotation),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
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

def ExactTapeOutputRanks : Prop :=
  ∀ (f ρ : Nat → Nat) (C : Nat) (raw xs : List Read)
    (annotations : List Annotation) (moved : List Read),
    NormalizedTape f ρ raw xs →
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    AlignedAnnotations f ρ terms values annotations →
    let ps := cohort f C terms annotations
    MovedAt f ρ (leastPrefix ps) ps moved →
    OriginalRanks raw (outsideCohort f C terms values annotations ++ moved)

def ExactTapeZeroTransition : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (C r : Nat) (constant : Int) (raw xs : List Read) (annotations : List Annotation),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
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

def FullActualNormalizedTapeZeroTransition : Prop :=
  ExactTapeZeroAssembly ∧ ExactTapeOutputRanks ∧ ExactTapeZeroTransition

end LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransition
