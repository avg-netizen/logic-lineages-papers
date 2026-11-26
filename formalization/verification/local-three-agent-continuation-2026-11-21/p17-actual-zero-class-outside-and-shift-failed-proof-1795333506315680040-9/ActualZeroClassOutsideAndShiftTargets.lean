module
public import LogicLineages.PermittedControl.ActualCountOriginDispositionsTargets
public import LogicLineages.PermittedControl.ActualZeroClassRecombinedRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassOutsideAndShift
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement
open ActualRankedZeroClass ActualWeightedReadNormalization ActualZeroClassRecombinedRow
open ActualCountOriginDispositions

def originalKeys (xs : List Read) : List LowerOperand := xs.map (fun rd => rd.1.2)

noncomputable def removeSelectedKeys (selected : List LowerOperand) (xs : List Read) : List Read := by
  classical
  exact xs.filter (fun rd => decide (rd.1.2 ∉ selected))

def weightedOriginShift (ledger : List (Origin × CountDisposition)) : Int :=
  (ledger.map (fun entry => entry.1.1.1.1 * entry.2.shift)).sum

/-- On the real normalized row, the outside list retains exactly the
original reads whose literal source keys lie outside the selected
full-value class. Source normalization already checked all raw reads. -/
def ExactOutsideClass : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (raw xs : List Read)
    (annotations : List Annotation),
    liftedReads f ρ raw → normalizeReads f ρ raw = some xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    outsideCohort f C xs annotations =
      removeSelectedKeys (originalKeys (classReads f C xs annotations)) xs

/-- Every original count contributes its own signed correction, and
an ended short prefix contributes its own recognized constant. The
aggregate is the literal shift installed by the actual replacement. -/
def ExactOriginShift : Prop :=
  ∀ (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (xs : List Read)
    (annotations : List Annotation) (anchor : Option ActualZeroClassCohortTransfer.SurvivingPrefix)
    (ledger : List (Origin × CountDisposition)) (out : List Read),
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations →
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger out →
    (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) annotations).2 = weightedOriginShift ledger

def FullActualZeroClassOutsideAndShift : Prop := ExactOutsideClass ∧ ExactOriginShift

end LogicLineages.PermittedControl.ActualZeroClassOutsideAndShift
