module
public import LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeysTargets
public import LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionAdmissibilityTargets
public import LogicLineages.PermittedControl.ActualZeroClassValueConservationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys ActualZeroClassCohortTransfer
open ActualZeroClassSelectedDispositionSums ActualZeroClassConcreteAssembly
open ActualZeroClassRecombinedRow ActualNormalizedTape

def ExactTapeDispositionSums : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation)
    (x₀ : Fin r) (q : NONote × NONote) (ledger : List DispositionEntry) (moved : List Read),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
    AnchorAt anchor x₀ q →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    let row := rankedRow r constant raw
    let S := (finiteClassColumns r (classReads f C xs annotations)).2
    let d := dispositionAt (keyedLedger r ledger)
    ((rankedRow r 0 moved).count =
       (∑ k ∈ S, (d k).term x₀ q (row.count k))) ∧
    ((replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 =
       (∑ k ∈ S, row.count k * (d k).shift))

def ExactTapeDispositionAdmissibility : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation)
    (x₀ : Fin r) (q : NONote × NONote) (ledger : List DispositionEntry) (moved : List Read),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
    AnchorAt anchor x₀ q →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    let S := (finiteClassColumns r (classReads f C xs annotations)).2
    let d := dispositionAt (keyedLedger r ledger)
    ∀ k ∈ S, (d k).Admissible x₀ k.2

def ExactTapeValueConservation : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C r : Nat) (constant : Int) (raw xs : List Read)
    (annotations : List Annotation) (moved : List Read),
    NormalizedTape f ρ raw xs →
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    AlignedAnnotations f ρ terms values annotations →
    Ready f B ρ C terms annotations →
    (rowParts f C terms values annotations).1 = 0 →
    let ps := cohort f C terms annotations
    MovedAt f ρ (leastPrefix ps) ps moved → liftedReads f ρ moved →
    let after := outsideCohort f C terms values annotations ++ moved
    let installed := constant + (replaceRow f C terms values annotations).2
    liftedReads f ρ after ∧
      concreteRow f C r constant xs annotations moved = rankedRow r installed after ∧
      constant + readSum raw = installed + readSum after

def FullActualNormalizedTapeDisposition : Prop :=
  ExactTapeDispositionSums ∧ ExactTapeDispositionAdmissibility ∧ ExactTapeValueConservation

end LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
