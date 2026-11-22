module
public import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeTargets
public import LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransitionTargets
public import LogicLineages.PermittedControl.ActualSymbolicZeroSuccessorTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessor
open scoped Classical
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualCanonicalOperandGrouping ActualSymbolicZeroSuccessor
open ActualFullValueLabels ActualFullLabelPairGuards ActualFiniteFullValueGuards
open ActualFullValueMaximalMetadata ActualZeroSuccessorMarkedClass
open ActualZeroClassReplacement ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualCountOriginDispositions
open ActualShortCountCleanup ActualShortCountCleanupCharge ActualRankedRowColumns
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets
open ActualZeroClassGroupedMovedCount (AnchorAt)

/-- The syntax for one given comparison vector in the supplied order.
No f, read payload or valuation is used to render the plan. -/
noncomputable def orderedSuccessor (constant : Int) (terms : List WeightedOperand)
    (a : List Answer) : Option SyntaxState := do
  if maximalCoefficient terms a = 0 then
    let ms ← decorate terms (classFlags (labels terms) a)
    successorFromMarks constant ms
  else none

noncomputable def canonicalSuccessor (constant : Int) (terms : List WeightedOperand)
    (a : List Answer) : Option SyntaxState :=
  orderedSuccessor constant (groupTyped terms) a

/-- Erasure statement applies to the very same moved reads at the own
chosen ordered first-tie anchor, not an existential alternate move. -/
def ExactOrderedSuccessorErasure : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C : Nat) (constant : Int) (xs : List Read)
    (anns : List Annotation) (a : List Answer) (moved : List Read),
    let terms := xs.map Prod.fst
    let vals := xs.map Prod.snd
    AlignedAnnotations f ρ terms vals anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    labels terms ≠ [] → Matches f ρ (pairs (labels terms)) a →
    (fullValues f anns).max? = some C → maximalCoefficient terms a = 0 →
    let ps := cohort f C terms anns
    MovedAt f ρ (leastPrefix ps) ps moved →
    let before := outsideCohort f C terms vals anns ++ moved
    let installed := constant + (replaceRow f C terms vals anns).2
    orderedSuccessor constant terms a =
      some ⟨installed + shortShift before,(retained before).map Prod.fst⟩

def ExactCanonicalSuccessorWitness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (C r : Nat) (constant : Int) (raw xs : List Read) (anns : List Annotation)
    (a : List Answer),
    liftedReads f ρ raw → (∀ rd ∈ raw, rd.1.2.rank < r) →
    normalizeCanonical f ρ raw = some xs →
    let terms := xs.map Prod.fst
    let vals := xs.map Prod.snd
    AlignedAnnotations f ρ terms vals anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    labels terms ≠ [] → Matches f ρ (pairs (labels terms)) a →
    (fullValues f anns).max? = some C →
    maximalCoefficient (groupTyped (raw.map Prod.fst)) a = 0 →
    Ready f B ρ C terms anns →
    let ps := cohort f C terms anns
    TransferReady B ρ ps →
    let anchor := leastPrefix ps
    ∃ (moved : List Read) (ledger : List DispositionEntry) (x₀ : Fin r) (q : NONote × NONote),
      MovedAt f ρ anchor ps moved ∧ liftedReads f ρ moved ∧ AnchorAt anchor x₀ q ∧
      DisposedOrigins f ρ anchor (countOrigins f C xs anns) ledger moved ∧
      ConcreteEquations f C r constant raw xs anns x₀ q ledger moved ∧
      let before := outsideCohort f C terms vals anns ++ moved
      let installed := constant + (replaceRow f C terms vals anns).2
      ZeroClassReplacement (rankedRow r constant raw) (rankedRow r installed before) ∧
      CleanedOutput f ρ r constant raw installed before ∧
      canonicalSuccessor constant (raw.map Prod.fst) a =
        some ⟨installed + shortShift before,(retained before).map Prod.fst⟩

def FullActualCanonicalSymbolicZeroSuccessor : Prop :=
  ExactOrderedSuccessorErasure ∧ ExactCanonicalSuccessorWitness

end LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessor
