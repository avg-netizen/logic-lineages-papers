module
public import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorTargets
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalZeroTrace
open scoped Classical
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualCanonicalOperandGrouping ActualCanonicalSymbolicZeroSuccessor
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualReadChargeIteration (ReadState ActiveAt NodeGuards RankBound stateValue stateCharge)
open ActualFullValueLabels ActualFullLabelPairGuards ActualFiniteFullValueGuards
open ActualFullValueMaximalMetadata ActualMixedRowLeadingAnnotations
open ActualZeroClassReplacement ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow
open ActualCountOriginDispositions ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly
open ActualZeroClassGroupedMovedCount (AnchorAt)
open ActualRankedRowColumns ActualZeroClassOutputState ActualShortCountCleanup
open ActualShortCountCleanupCharge InnerTerminationTargets

def eraseState (s : ReadState) : SyntaxState := ⟨s.constant,s.reads.map Prod.fst⟩

/-- Exact actual source conditions for one selected canonical zero step.
They do not assert any progress, chosen output or symbolic replay. -/
structure PreparedStep (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (s : ReadState) (xs : List Read) (anns : List Annotation) (C : Nat) (a : List Answer) : Prop where
  live : liftedReads f ρ s.reads
  ranks : RankBound r top s
  grouped : normalizeCanonical f ρ s.reads = some xs
  active : ActiveAt top xs
  guards : NodeGuards B ρ xs
  aligned : AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) anns
  nonempty : labels (xs.map Prod.fst) ≠ []
  matched : Matches f ρ (pairs (labels (xs.map Prod.fst))) a
  maximum : (fullValues f anns).max? = some C
  leadingFloor : f (ρ top) ≤ C
  zero : maximalCoefficient (groupTyped (s.reads.map Prod.fst)) a = 0
  ready : Ready f B ρ C (xs.map Prod.fst) anns
  transfer : TransferReady B ρ (cohort f C (xs.map Prod.fst) anns)

/-- Same actual ordered zero construction, exact semantic out fields.
No syntax equation is included as a premise of this witness. -/
def CanonicalZeroWitness (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (s t : ReadState) (a : List Answer) : Prop :=
  ∃ (xs : List Read) (anns : List Annotation) (C : Nat)
    (moved : List Read) (ledger : List DispositionEntry) (x₀ : Fin r) (q : NONote × NONote),
    PreparedStep f B ρ r top s xs anns C a ∧
    let terms := xs.map Prod.fst
    let vals := xs.map Prod.snd
    let ps := cohort f C terms anns
    let anchor := leastPrefix ps
    MovedAt f ρ anchor ps moved ∧ liftedReads f ρ moved ∧ AnchorAt anchor x₀ q ∧
    DisposedOrigins f ρ anchor (countOrigins f C xs anns) ledger moved ∧
    ConcreteEquations f C r s.constant s.reads xs anns x₀ q ledger moved ∧
    let before := outsideCohort f C terms vals anns ++ moved
    let installed := s.constant + (replaceRow f C terms vals anns).2
    ZeroClassReplacement (rankedRow r s.constant s.reads) (rankedRow r installed before) ∧
    CleanedOutput f ρ r s.constant s.reads installed before ∧
    t.constant = installed + shortShift before ∧ t.reads = retained before

inductive CanonicalTrace (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat) :
    List (List Answer) → ReadState → ReadState → Prop
  | nil (s : ReadState) : CanonicalTrace f B ρ r top [] s s
  | cons {a : List Answer} {answers : List (List Answer)} {s t u : ReadState} :
      CanonicalZeroWitness f B ρ r top s t a →
      CanonicalTrace f B ρ r top answers t u →
      CanonicalTrace f B ρ r top (a::answers) s u

/-- Purely symbolic replay of the chosen comparison sequence only.
Absence of a successor is retained as failure. -/
noncomputable def replay : List (List Answer) → SyntaxState → Option SyntaxState
  | [],s => some s
  | a::answers,s => do
    let t ← canonicalSuccessor s.constant s.terms a
    replay answers t

def ExactCanonicalZeroWitness : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (s : ReadState) (xs : List Read) (anns : List Annotation) (C : Nat) (a : List Answer),
    PreparedStep f B ρ r top s xs anns C a →
    ∃ t, CanonicalZeroWitness f B ρ r top s t a

def ExactCanonicalZeroReplay : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (s t : ReadState) (a : List Answer),
    CanonicalZeroWitness f B ρ r top s t a →
    canonicalSuccessor s.constant (eraseState s).terms a = some (eraseState t) ∧
    liftedReads f ρ t.reads ∧ RankBound r top t ∧ OriginalRanks s.reads t.reads ∧
    stateValue s = stateValue t ∧ stateCharge r t < stateCharge r s

def ExactCanonicalTraceReplay : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (s t : ReadState) (answers : List (List Answer)),
    CanonicalTrace f B ρ r top answers s t →
    replay answers (eraseState s) = some (eraseState t) ∧
    (liftedReads f ρ s.reads → liftedReads f ρ t.reads) ∧
    (RankBound r top s → RankBound r top t) ∧ OriginalRanks s.reads t.reads ∧
    stateValue s = stateValue t ∧ answers.length + stateCharge r t ≤ stateCharge r s

def FullActualCanonicalZeroTrace : Prop :=
  ExactCanonicalZeroWitness ∧ ExactCanonicalZeroReplay ∧ ExactCanonicalTraceReplay

end LogicLineages.PermittedControl.ActualCanonicalZeroTrace
