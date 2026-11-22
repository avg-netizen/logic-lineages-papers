module
public import LogicLineages.PermittedControl.ActualZeroClassConcreteAssemblyTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassValueConservation
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassConcreteAssembly

/-- The exact doubled signed equation does not require maximizing C.
Maximality is used for a separate logarithmic estimate, not this equality. -/
def ExactDoubledRowIdentity : Prop :=
  ∀ (f ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand) (values : List Nat)
    (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations →
    let parts := rowParts f C terms values annotations
    2 * actualSum terms values = parts.1 * (C : Int) + 2 * parts.2

/-- The given actual move ledger preserves the original cohort's signed
value, including the empty/ended branch and negative higher substitutions. -/
def ExactMovedValue : Prop :=
  ∀ (f ρ : Nat → Nat) (anchor : Option SurvivingPrefix)
    (ps : List SurvivingPrefix) (moved : List Read),
    MovedAt f ρ anchor ps moved →
    readSum (ps.map SurvivingPrefix.asRead) = readSum moved

/-- Preserve the value of this very witness, not merely the value of
some moved read list. The resulting correlated live reads are all paid
at the same original assignment. -/
def ExactConcreteValueConservation : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C r : Nat) (constant : Int) (raw xs : List Read)
    (annotations : List Annotation) (moved : List Read),
    liftedReads f ρ raw → normalizeReads f ρ raw = some xs →
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

def FullActualZeroClassValueConservation : Prop :=
  ExactDoubledRowIdentity ∧ ExactMovedValue ∧ ExactConcreteValueConservation

end LogicLineages.PermittedControl.ActualZeroClassValueConservation
