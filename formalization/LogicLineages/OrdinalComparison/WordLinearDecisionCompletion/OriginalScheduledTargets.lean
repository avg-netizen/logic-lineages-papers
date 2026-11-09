module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduledDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled.Targets

/-- Every original startup budget is allowed; no c+d+1<=t tail restriction. -/
def StepCorrect : Prop := ∀ c t index : Nat, ∀ a : NONote,
  Ordinal.omega0 ≤ a.1.repr →
    ONote.NF (rawNoteDecode (step c t index (rawNoteEncode a.1))) ∧
    (rawNoteDecode (step c t index (rawNoteEncode a.1))).repr =
      actualControlledStep (fun _ => KernelSourceCompletion.sourceBudget c t index) a.1.repr

def InitialCorrect : Prop := ∀ d : Nat,
  ONote.NF (rawNoteDecode (initial d)) ∧
    (rawNoteDecode (initial d)).repr = Ordinal.omega0 ^ (d : Ordinal)

def TrajectoryCorrect : Prop := ∀ c t : Nat, ∀ a : NONote, ∀ k : Nat,
  k ≤ actualScheduledCount (KernelSourceCompletion.sourceBudget c t) a.1.repr →
    ONote.NF (rawNoteDecode (run c t (rawNoteEncode a.1) k)) ∧
    (rawNoteDecode (run c t (rawNoteEncode a.1) k)).repr =
      actualScheduledStateAfter (KernelSourceCompletion.sourceBudget c t) a.1.repr k

def FirstFiniteExact : Prop := ∀ c t : Nat, ∀ a : NONote,
  actualScheduledCount (KernelSourceCompletion.sourceBudget c t) a.1.repr ∈
    search c t (rawNoteEncode a.1)

/-- Unbounded least search is only claimed partial recursive. -/
def PartialRecursive : Prop :=
  Partrec (fun p : (Nat × Nat) × Nat => countPartial p.1.1 p.1.2 p.2)

def PartialTotal : Prop := ∀ c t n : Nat, (countPartial c t n).Dom

def GenericCountCorrect : Prop := ∀ c t : Nat, ∀ a : NONote,
  countValue c t (rawNoteEncode a.1) =
    actualScheduledCount (KernelSourceCompletion.sourceBudget c t) a.1.repr

/-- The EXACT independently scheduled source count at EVERY natural input,
including points below all companion/tail calibration bounds. -/
def SourceCountCorrect : Prop := ∀ d c t : Nat,
  sourceCount d c t = KernelSourceCompletion.sourceCount d c t

def CountComputable : Prop :=
  Computable (fun p : (Nat × Nat) × Nat => countValue p.1.1 p.1.2 p.2)

def SourceCountComputable : Prop :=
  Computable (fun p : Nat × Nat × Nat => sourceCount p.1 p.2.1 p.2.2)

def StatePrograms : Prop :=
  Computable (fun p : Nat × Nat × Nat => KernelSourceCompletion.sourceBudget p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat × Nat => step p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Computable (fun p : Nat × Nat × Nat × Nat => run p.1 p.2.1 p.2.2.1 p.2.2.2)

def MalformedBehavior : Prop := ∀ c t n : Nat, rawNormalCode n ≠ 1 →
  countPartial c t n = Part.some 0 ∧ countValue c t n = 0

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduled.Targets
