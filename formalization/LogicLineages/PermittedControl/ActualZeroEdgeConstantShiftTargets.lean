module
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetTargets
public import LogicLineages.PermittedControl.ActualSignedReadMassTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroEdgeConstantShift
open FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualCountOriginDispositions ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualShortCountCleanup ActualReadChargeIteration
open ActualZeroClassCommonTail ActualZeroEdgeAlphabet ActualSignedReadMass

noncomputable def correctionMaximum (alphabet : List LowerOperand) : Nat :=
  finiteMax correctionBound alphabet

def prefixShortMaximum (alphabet : List LowerOperand) : Nat :=
  finiteMax (fun label => shortGapLength label.lam label.eta) (prefixCandidates alphabet)

/-- The intermediate literal reads may include actual short fields
discarded by the clean endpoint. Include the one-step expansion. -/
noncomputable def cleanupMaximum (alphabet : List LowerOperand) : Nat :=
  finiteMax shortLength (expand alphabet)

noncomputable def edgeFactor (alphabet : List LowerOperand) : Nat :=
  correctionMaximum alphabet + prefixShortMaximum alphabet + 3 * cleanupMaximum alphabet

/-- Alphabet coverage before, not merely after, short filtering. -/
def ExactPrecleanupAlphabet : Prop :=
  ∀ (f ρ : Nat → Nat) (C : Nat) (raw xs : List Read) (annotations : List Annotation)
    (moved : List Read) (alphabet : List LowerOperand),
    normalizeReads f ρ raw = some xs →
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    AlignedAnnotations f ρ terms values annotations →
    let ps := cohort f C terms annotations
    MovedAt f ρ (leastPrefix ps) ps moved →
    (∀ rd ∈ raw, rd.1.2 ∈ alphabet) →
    ∀ rd ∈ outsideCohort f C terms values annotations ++ moved, rd.1.2 ∈ expand alphabet

def ExactDispositionShiftBound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (anchor : Option SurvivingPrefix) (entry : Origin) (d : CountDisposition) (out : List Read)
    (alphabet : List LowerOperand),
    OriginPaid f B ρ C entry → OriginOutcome f ρ anchor entry d out →
    entry.1.1.2 ∈ alphabet →
    d.shift.natAbs ≤ correctionMaximum alphabet + prefixShortMaximum alphabet

def ExactCleanupShiftBound : Prop :=
  ∀ (before : List Read) (alphabet : List LowerOperand),
    (∀ rd ∈ before, rd.1.2 ∈ expand alphabet) →
    (shortShift before).natAbs ≤ signedMass before * cleanupMaximum alphabet

/-- Coarse per-edge estimate on the literal installed integer constant
for the same actual zero-class and cleanup witness. -/
def ExactActualConstantShift : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat) (source out : ReadState)
    (alphabet : List LowerOperand),
    ZeroEdge f B ρ r zRank source out → Covers alphabet source →
    (out.constant - source.constant).natAbs ≤ signedMass source.reads * edgeFactor alphabet ∧
    out.constant.natAbs ≤ source.constant.natAbs + signedMass source.reads * edgeFactor alphabet

def FullActualZeroEdgeConstantShift : Prop :=
  ExactPrecleanupAlphabet ∧ ExactDispositionShiftBound ∧
    ExactCleanupShiftBound ∧ ExactActualConstantShift

end LogicLineages.PermittedControl.ActualZeroEdgeConstantShift
