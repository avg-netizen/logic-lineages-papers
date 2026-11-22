module
public import LogicLineages.PermittedControl.ActualZeroClassOutsideAndShiftTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumns
open scoped Classical
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualZeroClassRecombinedRow

/-- The actual residual reads outside the selected class project to
exactly the filtered original columns. Both sides use the same literal
finite-rank syntax; ordinary linear terms still carry no charge. -/
def ExactOutsideRankedColumns : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C r : Nat) (constant : Int)
    (raw xs : List Read) (annotations : List Annotation),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    C ∈ fullValues f annotations →
    let row := rankedRow r constant raw
    let chosen := finiteClassColumns r (classReads f C xs annotations)
    let outside := rankedRow r 0 (outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) annotations)
    (outside.value = row.value.filter (fun k => k ∉ chosen.1)) ∧
    (outside.count = row.count.filter (fun k => k ∉ chosen.2))

end LogicLineages.PermittedControl.ActualZeroClassOutsideRankedColumns
