module
public import LogicLineages.PermittedControl.ActualShortCountCleanupChargeTargets
public import LogicLineages.PermittedControl.ActualZeroClassGuardedOneStepTargets
public import LogicLineages.PermittedControl.ActualLinearExitTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualReadChargeIteration
open scoped Classical
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualRankedRowColumns ActualZeroClassCohortTransfer
open ActualZeroClassRecombinedRow ActualCountOriginDispositions ActualZeroClassGroupedMovedCount
open ActualZeroClassSelectedCountKeys ActualZeroClassConcreteAssembly InnerTerminationTargets
open ActualZeroClassCommonTail ActualZeroClassOutputState ActualShortCountCleanup
open ActualShortCountCleanupCharge
open ActualLinearExit (exitRow OriginalSlots replay)

structure ReadState where
  constant : Int
  reads : List Read

def RankBound (r zRank : Nat) (s : ReadState) : Prop :=
  ∀ rd ∈ s.reads, rd.1.2.rank < r ∧ rd.1.2.rank ≤ zRank

def stateValue (s : ReadState) : Int := s.constant + readSum s.reads

noncomputable def stateCharge (r : Nat) (s : ReadState) : Nat :=
  let row := rankedRow r s.constant s.reads
  countCharge row + valueCount row

def ActiveAt (zRank : Nat) (xs : List Read) : Prop :=
  ∃ t ∈ xs.map Prod.fst, t.1 ≠ 0 ∧ t.2.rank = zRank ∧ NonlinearOperand t.2

def NodeGuards (B : Nat) (ρ : Nat → Nat) (xs : List Read) : Prop :=
  let terms := xs.map Prod.fst
  (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) ∧
  (∀ label ∈ prefixLabels terms, commonTail B terms ≤ ρ label.rank)

def ChosenClass (f ρ : Nat → Nat) (zRank : Nat) (xs : List Read)
    (annotations : List Annotation) (C : Nat) : Prop :=
  AlignedAnnotations f ρ (xs.map Prod.fst) (xs.map Prod.snd) annotations ∧
  (fullValues f annotations).max? = some C ∧ C ∈ fullValues f annotations ∧
  (∀ D ∈ fullValues f annotations, D ≤ C) ∧ f (ρ zRank) ≤ C

/-- Actual selected, guarded, strict-cleansed zero edge; not an
arbitrary lower-measure relation. The intermediate zero rewrite
and the literal short-count cleanup are on the very same witness. -/
def ZeroWitness (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat)
    (source out : ReadState) : Prop :=
  ∃ (xs : List Read) (annotations : List Annotation) (C : Nat)
    (moved : List Read) (ledger : List DispositionEntry) (x₀ : Fin r) (q : NONote × NONote),
    normalizeReads f ρ source.reads = some xs ∧ ActiveAt zRank xs ∧ NodeGuards B ρ xs ∧
    ChosenClass f ρ zRank xs annotations C ∧
    let terms := xs.map Prod.fst
    let values := xs.map Prod.snd
    let ps := cohort f C terms annotations
    let anchor := leastPrefix ps
    Ready f B ρ C terms annotations ∧ TransferReady B ρ ps ∧
    (rowParts f C terms values annotations).1 = 0 ∧
    MovedAt f ρ anchor ps moved ∧ liftedReads f ρ moved ∧ AnchorAt anchor x₀ q ∧
    DisposedOrigins f ρ anchor (countOrigins f C xs annotations) ledger moved ∧
    ConcreteEquations f C r source.constant source.reads xs annotations x₀ q ledger moved ∧
    let before := outsideCohort f C terms values annotations ++ moved
    let installed := source.constant + (replaceRow f C terms values annotations).2
    ZeroClassReplacement (rankedRow r source.constant source.reads) (rankedRow r installed before) ∧
    CleanedOutput f ρ r source.constant source.reads installed before ∧
    out.constant = installed + shortShift before ∧ out.reads = retained before

structure ZeroEdge (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat)
    (source out : ReadState) : Prop where
  actual : ZeroWitness f B ρ r zRank source out
  live : liftedReads f ρ out.reads
  ranks : OriginalRanks source.reads out.reads
  sameValue : stateValue source = stateValue out
  strict : stateCharge r out < stateCharge r source

inductive Trace (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat) :
    Nat → ReadState → ReadState → Prop
  | nil (s : ReadState) : Trace f B ρ r zRank 0 s s
  | cons {n : Nat} {s t u : ReadState} :
      ZeroEdge f B ρ r zRank s t → Trace f B ρ r zRank n t u → Trace f B ρ r zRank (n+1) s u

def LinearTerminal (f ρ : Nat → Nat) (zRank : Nat) (constant : Int)
    (raw xs : List Read) : Prop :=
  let retained := ActualLinearExit.lowerReads zRank xs
  let ops := ActualLinearExit.table zRank xs
  let row := exitRow zRank constant xs
  PreparedInput ops (.atom (.nonnegative row)) ∧
  (∃ ν : Nat → Nat, OriginalSlots ν retained ∧ PreparedTableTied f zRank ρ ops ν) ∧
  (∀ ν : Nat → Nat, PreparedTableTied f zRank ρ ops ν →
    OriginalSlots ν retained ∧
    (∀ (j : Nat) (hj : j < ops.length),
      lowerOperandRead f ρ ops[j] = some (some (ν (j+1)))) ∧
    (∀ z : Nat, PreparedTableTied f zRank (Function.update ρ zRank z) ops
        (Function.update ν 0 z) ∧
      liftedReads f (Function.update ρ zRank z) (replay zRank z xs) ∧
      NormalForm.rowValue row (Function.update ν 0 z) =
        constant + readSum (replay zRank z xs)) ∧
    NormalForm.rowValue row (Function.update ν 0 (ρ zRank)) = constant + readSum raw)

def NonzeroTerminal (f ρ : Nat → Nat) (zRank : Nat) (s : ReadState) (xs : List Read) : Prop :=
  ∃ (annotations : List Annotation) (C : Nat),
    ChosenClass f ρ zRank xs annotations C ∧
    let terms := xs.map Prod.fst
    let parts := rowParts f C terms (xs.map Prod.snd) annotations
    let R := stateValue s
    let E := s.constant + parts.2
    parts.1 ≠ 0 ∧ 2 * R = parts.1 * (C : Int) + 2 * E ∧
    E.natAbs ≤ slopeBound terms * Nat.log2 C + (s.constant.natAbs + offsetBound terms) ∧
    (SelectedLeadingSignCutoff.cutoff (slopeBound terms) (s.constant.natAbs + offsetBound terms)
        ≤ ρ zRank →
      (0 < R ↔ 0 < parts.1) ∧ (R < 0 ↔ parts.1 < 0) ∧
      (0 ≤ R ↔ 0 < parts.1) ∧ R ≠ 0)

def Terminal (f ρ : Nat → Nat) (zRank : Nat) (s : ReadState) : Prop :=
  ∃ xs, normalizeReads f ρ s.reads = some xs ∧
    ((¬ ActiveAt zRank xs ∧ LinearTerminal f ρ zRank s.constant s.reads xs) ∨
      (ActiveAt zRank xs ∧ NonzeroTerminal f ρ zRank s xs))

/-- Numerical annotation and pair-tail supply only at actual reached
nonlinear nodes and their exact normalization. No terminal or trace
existence, successful annotation, or next-node closure is assumed. -/
def ReachedGuardSupply (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat)
    (initial : ReadState) : Prop :=
  ∀ (n : Nat) (s : ReadState), Trace f B ρ r zRank n initial s →
    ∀ xs, normalizeReads f ρ s.reads = some xs → ActiveAt zRank xs → NodeGuards B ρ xs

def ExactReadProgress : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (s : ReadState), liftedReads f ρ s.reads → RankBound r zRank s →
    (∀ xs, normalizeReads f ρ s.reads = some xs → ActiveAt zRank xs → NodeGuards B ρ xs) →
    Terminal f ρ zRank s ∨ ∃ t, ZeroEdge f B ρ r zRank s t

/-- Fixed-assignment, actual conditional normalization. The step count
is bounded by the original exact charge, not by a supplied fuel. -/
def ExactReadChargeIteration : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r zRank : Nat) (initial : ReadState), liftedReads f ρ initial.reads →
    RankBound r zRank initial → ReachedGuardSupply f B ρ r zRank initial →
    ∃ (n : Nat) (final : ReadState), Trace f B ρ r zRank n initial final ∧
      n ≤ stateCharge r initial ∧ Terminal f ρ zRank final ∧
      liftedReads f ρ final.reads ∧ RankBound r zRank final ∧
      OriginalRanks initial.reads final.reads ∧ stateValue initial = stateValue final

def FullActualReadChargeIteration : Prop :=
  ExactReadProgress ∧ ExactReadChargeIteration

end LogicLineages.PermittedControl.ActualReadChargeIteration
