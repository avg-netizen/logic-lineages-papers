module
public import LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionSumsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionAdmissibility
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys ActualZeroClassCohortTransfer
open ActualZeroClassSelectedDispositionSums

/-- Every selected, actual source key has its own disposition from the
ordered ledger. Its rank obeys the source's ended/same/higher distinction,
not an assumption on any lower target key. -/
def ExactSelectedDispositionAdmissibility : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation) (anchor : Option SurvivingPrefix)
    (x₀ : Fin r) (q : NONote × NONote) (ledger : List DispositionEntry) (moved : List Read),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations → AnchorAt anchor x₀ q →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved →
    let S := (finiteClassColumns r (classReads f C xs annotations)).2
    let d := dispositionAt (keyedLedger r ledger)
    ∀ k ∈ S, (d k).Admissible x₀ k.2

end LogicLineages.PermittedControl.ActualZeroClassSelectedDispositionAdmissibility
