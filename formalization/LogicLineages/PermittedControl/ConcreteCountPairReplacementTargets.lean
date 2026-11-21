module
public import LogicLineages.PermittedControl.CountTransferTargets
public import LogicLineages.PermittedControl.ThresholdTargets
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ConcreteCountPairReplacement
open OrdinalComparison PreparedProjection FieldComparison

/-- Syntactic H=(lambdaQ,muQ+deltaP) at the SAME original lower raw rank.
The code depends only on interval syntax and the retained rank, never rho. -/
def replacementCode (r0 : Nat) (p : IntervalPairCodes) : LowerOperandCode :=
  (2,r0,(1,0,p.2.1,ordinalAddCode p.2.2 (ordinalSubCode p.1.1 p.1.2)))

noncomputable def replacementOperand (r0 : Nat) (lp mp lq mq : NONote) : LowerOperand :=
  .count r0 lq (mq + (lp - mp))

/-- Pay BOTH the inverse-table and original P-versus-Q gap-comparison
thresholds. No unproved dominance of one tail by the other is assumed. -/
def safeTailCode (p : IntervalPairCodes) (B : Nat) : Nat :=
  max (inverseTableTailCode p.2.1 p.2.2 p.1.2 (ordinalSubCode p.1.1 p.1.2) B)
    (encodedGapInputTail (p.1.1,p.1.2,p.2.1,p.2.2,0))

def CodeExact : Prop :=
  Primrec₂ replacementCode ∧ Primrec₂ safeTailCode ∧
  (∀ (r0 : Nat) (lp mp lq mq : NONote),
    replacementCode r0 (intervalPairCodes lp mp lq mq) = (replacementOperand r0 lp mp lq mq).code) ∧
  ∀ (lp mp lq mq : NONote) (B : Nat),
    safeTailCode (intervalPairCodes lp mp lq mq) B =
      max (inverseTableTail lq mq mp (lp-mp) B)
        (gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0)

/-- One actual collision pair only. The full cores, actual original hit
counts, original raw arguments and integer signs are retained. H success
and gap ordering are conclusions; no collision-certificate sign is assumed. -/
def ActualPairReplacement : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lp mp lq mq : NONote), Targets.ProperIntervalNotes lp mp → Targets.ProperIntervalNotes lq mq →
  ∀ (ρ : Nat → Nat) (r0 r1 p q : Nat),
    let x := ρ r0
    let y := ρ r1
    safeTailCode (intervalPairCodes lp mp lq mq) B ≤ x →
    safeTailCode (intervalPairCodes lp mp lq mq) B ≤ y → x < y →
    FirstEntry f (countInitial lq.1.repr x) mq.1.repr p →
    FirstEntry f (countInitial lp.1.repr y) mp.1.repr q →
    f (entryNormAt f (countInitial lp.1.repr y) q) =
      f (entryNormAt f (countInitial lq.1.repr x) p) →
    let delta := lp-mp
    let kappa := mq+delta
    let H := replacementOperand r0 lp mp lq mq
    delta.1.repr < (lq-mq).1.repr ∧
    mq.1.repr < kappa.1.repr ∧ kappa.1.repr < lq.1.repr ∧
    Targets.ProperIntervalNotes lq kappa ∧ H.rank = r0 ∧
    ∃ i : Nat,
      FirstEntry f (countInitial lq.1.repr x) kappa.1.repr i ∧
      entryNormAt f (countInitial lq.1.repr x) i = y ∧
      (y,i) ∈ fixedEntryProgram f (rawNoteEncode lq.1,
        ordinalAddCode (rawNoteEncode mq.1) (rawNoteEncode delta.1),x) ∧
      p = i+q ∧ (q : Int) = (p : Int)-(i : Int) ∧
      ClosedOrdinaryValueDomain (.entry 0 lq kappa) x ∧
      LowerOperandActual f ρ H i ∧
      closedOrdinaryCountField f (rawNoteEncode lq.1,
        ordinalAddCode (rawNoteEncode mq.1) (rawNoteEncode delta.1),x) = some (some i)

/-- Concrete pair supplier for printed rank-transfer only. No arbitrary
class, chosen minimum, Finsupp surgery, charge descent or whole #703/#702. -/
def FullConcretePairReplacement : Prop := CodeExact ∧ ActualPairReplacement
end LogicLineages.PermittedControl.ConcreteCountPairReplacement
