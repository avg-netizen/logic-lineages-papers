module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteCharge
open scoped Classical
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets

/-- One actual original zero-class rewrite has nonincreasing count charge and
ordinary value count, with a strict decrease in their sum. The inequalities
hold for the literal concrete row obtained from the very same moved reads
and structural witness. -/
def ExactConcreteZeroClassCharge : Prop :=
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
      let src := rankedRow r constant raw
      let out := concreteRow f C r constant xs annotations moved
      ZeroClassReplacement src out ∧
      countCharge out ≤ countCharge src ∧
      valueCount out ≤ valueCount src ∧
      countCharge out + valueCount out < countCharge src + valueCount src

end LogicLineages.PermittedControl.ActualZeroClassConcreteCharge
