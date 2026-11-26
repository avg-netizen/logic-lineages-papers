module
public import LogicLineages.PermittedControl.ActualCountOriginDispositionsTargets
public import Mathlib.Data.List.Forall2

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassSelectedCountKeys
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions ActualZeroClassCohortTransfer

abbrev DispositionEntry := Origin × CountDisposition
abbrev KeyedDisposition (r : Nat) := CountKey r × CountDisposition

/-- Reindex the ordered actual ledger by literal original count keys.
The lower interval from the disposition is never used as a key. -/
def keyedLedger (r : Nat) (ledger : List DispositionEntry) : List (KeyedDisposition r) :=
  ledger.filterMap fun item =>
    match finiteClassKey r item.1.1.1.2 with
    | some (.inr k) => some (k,item.2)
    | _ => none

def KeyedMatch {r : Nat} (row : RankedRow r) (item : DispositionEntry)
    (indexed : KeyedDisposition r) : Prop :=
  item.1.1.1.2 = countOperand r indexed.1 ∧
    item.1.1.1.1 = row.count indexed.1 ∧ item.2 = indexed.2

noncomputable def keyedSet {r : Nat} (ledger : List (KeyedDisposition r)) : Finset (CountKey r) := by
  classical
  exact (ledger.map Prod.fst).toFinset

/-- All and only the actual selected source count keys occur once in the
indexed ledger, in original order with exactly the original normalized
row coefficient and its own disposition. No lowered key is compared. -/
def ExactSelectedCountKeyLedger : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation) (anchor : Option SurvivingPrefix)
    (ledger : List DispositionEntry) (moved : List Read),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    let indexed := keyedLedger r ledger
    ledger.map Prod.fst = countOrigins f C xs annotations ∧
    List.Forall₂ (KeyedMatch (rankedRow r constant raw)) ledger indexed ∧
    (indexed.map Prod.fst).Nodup ∧
    keyedSet indexed = (finiteClassColumns r (classReads f C xs annotations)).2

end LogicLineages.PermittedControl.ActualZeroClassSelectedCountKeys
