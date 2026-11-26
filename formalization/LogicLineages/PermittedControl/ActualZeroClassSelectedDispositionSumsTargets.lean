module
public import LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCountTargets
public import LogicLineages.PermittedControl.ActualZeroClassSelectedCountKeysTargets
public import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionSums
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys ActualZeroClassCohortTransfer

/-- Lookup only literal original CountKeys. The default outside the selected
set is dummy; no actual contribution is ever assigned to an unlisted key. -/
noncomputable def dispositionAt {r : Nat} :
    List (KeyedDisposition r) → CountKey r → CountDisposition
  | [],_ => .ended 0
  | item::rest,k => by
      classical
      exact if k = item.1 then item.2 else dispositionAt rest k

/-- On the actual source cohort, both the grouped moved column and the
actually installed signed shift are finite sums indexed by the original
selected CountKeys and exact original coefficients. -/
def ExactSelectedDispositionSums : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation) (anchor : Option SurvivingPrefix)
    (x₀ : Fin r) (q : NONote × NONote) (ledger : List DispositionEntry) (moved : List Read),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations → AnchorAt anchor x₀ q →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    let row := rankedRow r constant raw
    let S := (finiteClassColumns r (classReads f C xs annotations)).2
    let d := dispositionAt (keyedLedger r ledger)
    ((rankedRow r 0 moved).count =
       (∑ k ∈ S, (d k).term x₀ q (row.count k))) ∧
    ((replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 =
       (∑ k ∈ S, row.count k * (d k).shift))

end LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionSums
