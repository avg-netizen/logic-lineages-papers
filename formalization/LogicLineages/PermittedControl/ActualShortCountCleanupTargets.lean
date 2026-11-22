module
public import LogicLineages.PermittedControl.ActualZeroClassOutputStateTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualShortCountCleanup
open OrdinalComparison FieldComparison PreparedProjection
open ActualZeroClassReplacement ActualZeroClassOutputState

def shortLength : LowerOperand → Nat
  | .count _ lam mu => shortGapLength lam mu
  | _ => 0

/-- The original ordered list, with precisely the positive short
count occurrences removed. Ordinary value fields are not cleaned. -/
def retained (reads : List Read) : List Read :=
  reads.filter (fun rd => decide (shortLength rd.1.2 = 0))

def shortShift : List Read → Int
  | [] => 0
  | rd :: rs => rd.1.1 * (shortLength rd.1.2 : Int) + shortShift rs

/-- The actual short count is the literal recognized finite gap.
No new uniform tail is required for a count which already has its
actual closed proper read. -/
def ExactPositiveShortCount : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (rank : Nat) (lam mu : NONote) (v : Nat),
    0 < shortGapLength lam mu → LowerOperandActual f ρ (.count rank lam mu) v →
    v = shortGapLength lam mu

/-- True identity prefixes were consumed during the original
replacement. An equal-endpoint putative emitted closed count is
invalid, not a successful zero count. Every proper live count is
strictly positive regardless of its signed coefficient. -/
def ExactIdentityBoundary : Prop :=
  (∀ (f ρ : Nat → Nat) (rank : Nat) (lam mu : NONote) (v : Nat),
    LowerOperandActual f ρ (.count rank lam mu) v → 0 < v) ∧
  ∀ (f ρ : Nat → Nat) (rank : Nat) (lam mu : NONote),
    lam.1.repr = mu.1.repr →
    lowerOperandRead f ρ (.count rank lam mu) = none ∧
    ∀ v : Nat, ¬ LowerOperandActual f ρ (.count rank lam mu) v

/-- Long shape only. Genuine next-annotation affordability is a
separate numerical requirement, not a consequence of shape. -/
def LongCountOperand : LowerOperand → Prop
  | .count _ lam mu => LongField (.entry 0 lam mu)
  | _ => True

def ExactShortCountCleanup : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (constant : Int) (raw before : List Read),
    liftedReads f ρ before →
    let after := retained before
    let installed := constant + shortShift before
    after.Sublist before ∧ liftedReads f ρ after ∧
    (∀ rd ∈ after, LongCountOperand rd.1.2) ∧
    (OriginalRanks raw before → OriginalRanks raw after) ∧
    constant + readSum before = installed + readSum after

def FullActualShortCountCleanup : Prop :=
  ExactPositiveShortCount ∧ ExactIdentityBoundary ∧ ExactShortCountCleanup

end LogicLineages.PermittedControl.ActualShortCountCleanup
