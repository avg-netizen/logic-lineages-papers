module
public import LogicLineages.PermittedControl.ActualZeroClassSelectedCountKeysTargets
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeys
open ActualNormalizedTape ActualZeroClassSelectedCountKeys
open ActualZeroClassReplacement ActualMixedRowLeadingAnnotations
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions
open ActualZeroClassCohortTransfer

/-- Reindex the genuine actual ledger at the chosen ordered tape's own
least surviving prefix. No transfer of a different tape's anchor or
disposition list is assumed. All keys still belong to the source. -/
def ExactTapeSelectedCountKeyLedger : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation)
    (ledger : List DispositionEntry) (moved : List Read),
    (∀ rd ∈ raw, rd.1.2.rank < r) → NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    let indexed := keyedLedger r ledger
    ledger.map Prod.fst = countOrigins f C xs annotations ∧
    List.Forall₂ (KeyedMatch (rankedRow r constant raw)) ledger indexed ∧
    (indexed.map Prod.fst).Nodup ∧
    keyedSet indexed = (finiteClassColumns r (classReads f C xs annotations)).2

end LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeys
