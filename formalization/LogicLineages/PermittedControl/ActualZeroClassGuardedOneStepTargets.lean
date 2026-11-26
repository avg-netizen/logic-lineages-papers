module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteChargeTargets
public import LogicLineages.PermittedControl.ActualZeroClassCommonTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassGuardedOneStep
open scoped Classical
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets
open ActualZeroClassCommonTail

/-- The same existential body as the concrete charge theorem, now tied
to the actual maximum annotation class of the source node. -/
def ChargedRewrite (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation) : Prop :=
  let ps := cohort f C (xs.map Prod.fst) annotations
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

/-- Select the actual maximum after checked grouping of original reads.
Split by the literal signed doubled coefficient at that maximum; the
zero branch rewrites that class, and the nonzero branch keeps its exact
arithmetic decomposition and gives the sign only on its own cutoff. -/
def ExactGuardedZeroClassOneStep : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (constant : Int) (raw xs : List Read),
    liftedReads f ρ raw →
    (∀ rd ∈ raw, rd.1.2.rank < r ∧ rd.1.2.rank ≤ zRank) →
    normalizeReads f ρ raw = some xs →
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    (∃ t ∈ terms, t.1 ≠ 0 ∧ t.2.rank = zRank ∧ NonlinearOperand t.2) →
    (∀ label ∈ prefixLabels terms, commonTail B terms ≤ ρ label.rank) →
    ∃ annotations C, AlignedAnnotations f ρ terms values annotations ∧
      (fullValues f annotations).max? = some C ∧
      C ∈ fullValues f annotations ∧ (∀ D ∈ fullValues f annotations, D ≤ C) ∧
      f (ρ zRank) ≤ C ∧
      Ready f B ρ C terms annotations ∧ TransferReady B ρ (cohort f C terms annotations) ∧
      let parts := rowParts f C terms values annotations
      let R := constant + readSum raw
      let E := constant + parts.2
      (parts.1 = 0 ∧ ChargedRewrite f ρ C r constant raw xs annotations) ∨
      (parts.1 ≠ 0 ∧ 2 * R = parts.1 * (C : Int) + 2 * E ∧
        E.natAbs ≤ slopeBound terms * Nat.log2 C + (constant.natAbs + offsetBound terms) ∧
        (SelectedLeadingSignCutoff.cutoff (slopeBound terms) (constant.natAbs + offsetBound terms)
            ≤ ρ zRank →
          (0 < R ↔ 0 < parts.1) ∧ (R < 0 ↔ parts.1 < 0) ∧
          (0 ≤ R ↔ 0 < parts.1) ∧ R ≠ 0))

end LogicLineages.PermittedControl.ActualZeroClassGuardedOneStep
