module
public import LogicLineages.PermittedControl.ActualCanonicalZeroTraceTargets
public import LogicLineages.PermittedControl.ActualNormalizedTapeTargets
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalZeroAlphabet
open PreparedProjection
open ActualReadChargeIteration (ReadState)
open ActualZeroClassReplacement ActualMixedRowLeadingAnnotations
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow ActualCountOriginDispositions
open ActualNormalizedTape ActualCanonicalZeroTrace ActualZeroEdgeAlphabet
open ActualFullLabelPairGuards (Answer)

/-- Includes intermediate moved labels actually removed by short-count
cleanup, not only the surviving next-state syntax. -/
def ExactCertifiedExpansion : Prop :=
  ∀ (f ρ : Nat → Nat) (C : Nat) (raw xs moved : List Read) (anns : List Annotation)
    (alphabet : List LowerOperand),
    NormalizedTape f ρ raw xs →
    AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) anns →
    let ps := cohort f C (xs.map Prod.fst) anns
    MovedAt f ρ (leastPrefix ps) ps moved →
    (∀ rd ∈ raw, rd.1.2 ∈ alphabet) →
    ∀ rd ∈ outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) anns ++ moved,
      rd.1.2 ∈ expand alphabet

def ExactCanonicalZeroAlphabet : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (s t : ReadState) (answer : List Answer) (alphabet : List LowerOperand),
    CanonicalZeroWitness f B ρ r top s t answer → Covers alphabet s →
    Covers (expand alphabet) t

def ExactCanonicalTraceAlphabet : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (s t : ReadState) (answers : List (List Answer)) (alphabet : List LowerOperand),
    CanonicalTrace f B ρ r top answers s t → Covers alphabet s →
    Covers (expandSteps answers.length alphabet) t

def FullActualCanonicalZeroAlphabet : Prop :=
  ExactCertifiedExpansion ∧ ExactCanonicalZeroAlphabet ∧ ExactCanonicalTraceAlphabet

end LogicLineages.PermittedControl.ActualCanonicalZeroAlphabet
