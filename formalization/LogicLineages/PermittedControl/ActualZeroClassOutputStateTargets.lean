module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteChargeTargets
public import LogicLineages.PermittedControl.ActualZeroClassValueConservationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutputState
open scoped Classical
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets

/-- Every emitted rank is an original raw rank, including a lower H
emitted at the actual least surviving prefix. It is not a new index. -/
def OriginalRanks (raw after : List Read) : Prop :=
  ∀ rd ∈ after, ∃ prior ∈ raw, rd.1.2.rank = prior.1.2.rank

def ExactOutputRankProvenance : Prop :=
  ∀ (f ρ : Nat → Nat) (C : Nat) (raw xs : List Read)
    (annotations : List Annotation) (moved : List Read),
    liftedReads f ρ raw → normalizeReads f ρ raw = some xs →
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    AlignedAnnotations f ρ terms values annotations →
    let ps := cohort f C terms annotations
    MovedAt f ρ (leastPrefix ps) ps moved →
    OriginalRanks raw (outsideCohort f C terms values annotations ++ moved)

/-- The literal, value-preserving concrete zero-step output and strict
charge on the same witness. Long-count annotation for the next node,
including cleanup of new short H counts, is not part of this state. -/
def ExactConcreteOutputState : Prop :=
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
      countCharge out + valueCount out < countCharge src + valueCount src

def FullActualZeroClassOutputState : Prop :=
  ExactOutputRankProvenance ∧ ExactConcreteOutputState

end LogicLineages.PermittedControl.ActualZeroClassOutputState
