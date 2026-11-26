module
public import LogicLineages.PermittedControl.ActualNormalizedTapeDispositionTargets
import LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCountProof
import LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeysProof
import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftConstantProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys ActualZeroClassCohortTransfer
open ActualZeroClassOutsideAndShift ActualZeroClassSelectedDispositionSums

open ActualNormalizedTape ActualNormalizedTapeSelectedCountKeys

private theorem lookupHead {r : Nat} (item : KeyedDisposition r)
    (tail : List (KeyedDisposition r)) :
    dispositionAt (item::tail) item.1 = item.2 := by
  simp [dispositionAt]

private theorem lookupTail {r : Nat} (item : KeyedDisposition r)
    (tail : List (KeyedDisposition r)) (k : CountKey r) (ne : k ≠ item.1) :
    dispositionAt (item::tail) k = dispositionAt tail k := by
  simp [dispositionAt,ne]

private theorem selectedLedgerSum {r : Nat} {A : Type} [AddCommMonoid A]
    (φ : CountKey r → CountDisposition → A) (indexed : List (KeyedDisposition r))
    (unique : (indexed.map Prod.fst).Nodup) :
    (indexed.map (fun item => φ item.1 item.2)).sum =
      ∑ k ∈ keyedSet indexed, φ k (dispositionAt indexed k) := by
  classical
  induction indexed with
  | nil => simp [keyedSet]
  | cons item tail ih =>
      have hnd : (item.1 :: tail.map Prod.fst).Nodup := unique
      obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp hnd
      have hf : item.1 ∉ keyedSet tail := by simpa only [keyedSet,List.mem_toFinset] using fresh
      have hs : keyedSet (item::tail) = insert item.1 (keyedSet tail) := by
        simp [keyedSet,List.toFinset_cons]
      have htail :
          (∑ k ∈ keyedSet tail, φ k (dispositionAt tail k)) =
          ∑ k ∈ keyedSet tail, φ k (dispositionAt (item::tail) k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hne : k ≠ item.1 := by
          intro h; exact hf (h ▸ hk)
        rw [lookupTail item tail k hne]
      simp only [List.map_cons,List.sum_cons,hs,Finset.sum_insert hf,lookupHead]
      rw [ih tailUnique,htail]

private theorem sourceLedgerSum {r : Nat} {A : Type} [AddCommMonoid A]
    (row : RankedRow r) (φ : Int → CountDisposition → A)
    (ledger : List DispositionEntry) (indexed : List (KeyedDisposition r))
    (actual : List.Forall₂ (KeyedMatch row) ledger indexed) :
    (ledger.map (fun item => φ item.1.1.1.1 item.2)).sum =
      (indexed.map (fun item => φ (row.count item.1) item.2)).sum := by
  induction actual with
  | nil => rfl
  | cons head _ ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [head.2.1,head.2.2,ih]

theorem exactTapeDispositionSums : ExactTapeDispositionSums := by
  intro f ρ C r constant raw xs annotations x₀ q ledger moved bounded tape aligned present
  dsimp only
  intro anchorAt disposed
  let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
  let row := rankedRow r constant raw
  let indexed := keyedLedger r ledger
  let S := (finiteClassColumns r (classReads f C xs annotations)).2
  obtain ⟨_,matched,unique,keys⟩ :=
    exactTapeSelectedCountKeyLedger f ρ C r constant raw xs annotations ledger moved
      bounded tape aligned present disposed
  constructor
  · have hm := exactGroupedMovedCount f ρ C r xs annotations anchor x₀ q ledger moved anchorAt disposed
    calc
      (rankedRow r 0 moved).count = movedCountTerms x₀ q ledger := hm
      _ = (indexed.map (fun item => item.2.term x₀ q (row.count item.1))).sum :=
        sourceLedgerSum row (fun w d => d.term x₀ q w) ledger indexed matched
      _ = ∑ k ∈ keyedSet indexed, (dispositionAt indexed k).term x₀ q (row.count k) :=
        selectedLedgerSum (fun k d => d.term x₀ q (row.count k)) indexed unique
      _ = ∑ k ∈ S, (dispositionAt indexed k).term x₀ q (row.count k) := by
        rw [show keyedSet indexed = S from keys]
  · have hs := exactOriginShift f ρ C xs annotations anchor ledger moved aligned disposed
    calc
      (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 =
          weightedOriginShift ledger := hs
      _ = (indexed.map (fun item => row.count item.1 * item.2.shift)).sum :=
        sourceLedgerSum row (fun w d => w * d.shift) ledger indexed matched
      _ = ∑ k ∈ keyedSet indexed, row.count k * (dispositionAt indexed k).shift :=
        selectedLedgerSum (fun k d => row.count k * d.shift) indexed unique
      _ = ∑ k ∈ S, row.count k * (dispositionAt indexed k).shift := by
        rw [show keyedSet indexed = S from keys]

end LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
