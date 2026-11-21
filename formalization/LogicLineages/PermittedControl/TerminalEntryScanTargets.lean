module
public import LogicLineages.PermittedControl.EntryTargets
public import LogicLineages.PermittedControl.EvaluatorTargets

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- A legal raw start is a normal note. A legal raw target is a normal
note equal to its own limit part, hence zero or a positive limit.
Reject positive finite tails and all nonnormal input explicitly. -/
def terminalScanGuard (p : Nat × Nat) : Bool :=
  decide (rawNormalCode p.1 = 1 ∧ rawNormalCode p.2 = 1 ∧ (rawSplitCode p.2).unpair.1 = p.2)

/-- Literal predicate of the existing encoded entry search. -/
def terminalScanTest (f : Nat → Nat) (n mu i : Nat) : Bool :=
  decide ((rawSplitCode (encodedStatesWith f n i)).unpair.1 = mu)

/-- Inclusive prefix scan. Zero means no index yet; a positive result
is the earliest index plus one, not a sentinel hit or output value. -/
def boundedTerminalEntryIndex (f : Nat → Nat) (n mu : Nat) : Nat → Nat
  | 0 => if terminalScanTest f n mu 0 then 1 else 0
  | T + 1 =>
      let old := boundedTerminalEntryIndex f n mu T
      if old = 0 then
        if terminalScanTest f n mu (T + 1) then T + 2 else 0
      else old

/-- Three disjoint results: rejected input, genuine miss, or exact hit.
Only the hit carries a norm and an index. -/
abbrev TerminalEntryScanResult := Option (Option (Nat × Nat))

def terminalScanAt (f : Nat → Nat) (p : Nat × Nat) (T : Nat) : TerminalEntryScanResult :=
  match boundedTerminalEntryIndex f p.1 p.2 T with
  | 0 => some none
  | i + 1 => some (some (rawNormCode (encodedStatesWith f p.1 i),i))

/-- Real guarded program. It obtains the actual terminal index, then
runs the inclusive scan; invalid inputs never run an unbounded search. -/
def terminalEntryScanProgram (f : Nat → Nat) (p : Nat × Nat) : Part TerminalEntryScanResult :=
  if terminalScanGuard p then
    (terminalSearchWith f p.1).map (terminalScanAt f p)
  else Part.some none

/-- Definite realization in Lean. The separate domain theorem requires
the guarded program to be defined on *all* codes, so no use of this
representation's fallback is allowed to mask divergence or a miss. -/
noncomputable def terminalEntryScanWith (f : Nat → Nat) (p : Nat × Nat) : TerminalEntryScanResult := by
  classical
  exact (terminalEntryScanProgram f p).getOrElse none

namespace Targets

def TerminalEntryScanGuardExact : Prop :=
  Primrec terminalScanGuard ∧
  ∀ p : Nat × Nat, terminalScanGuard p = true ↔
    ONote.NF (rawNoteDecode p.1) ∧ ONote.NF (rawNoteDecode p.2) ∧
      ((rawNoteDecode p.2).repr = 0 ∨ Order.IsSuccLimit (rawNoteDecode p.2).repr)

def BoundedTerminalEntryIndexExact : Prop :=
  ∀ (f : Nat → Nat) (n mu T : Nat),
    (boundedTerminalEntryIndex f n mu T = 0 ↔
      ∀ i : Nat, i ≤ T → terminalScanTest f n mu i = false) ∧
    ∀ i : Nat, boundedTerminalEntryIndex f n mu T = i + 1 ↔
      i ≤ T ∧ terminalScanTest f n mu i = true ∧
        ∀ j : Nat, j < i → terminalScanTest f n mu j = false

/-- Domain for arbitrary actual f and all input codes; guarded total
computability uniformly relative to a computable f. -/
def TerminalEntryScanEffective : Prop :=
  ∀ f : Nat → Nat,
    (∀ p : Nat × Nat, (terminalEntryScanProgram f p).Dom) ∧
    (Computable f →
      Computable (fun p : Nat × Nat × Nat => boundedTerminalEntryIndex f p.1 p.2.1 p.2.2) ∧
      Partrec (terminalEntryScanProgram f) ∧ Computable (terminalEntryScanWith f))

def TerminalEntryScanActual : Prop :=
  (∀ (f : Nat → Nat) (p : Nat × Nat),
    terminalEntryScanWith f p = none ↔ terminalScanGuard p = false) ∧
  (∀ (f : Nat → Nat) (a mu : NONote),
    (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) →
    let p := (rawNoteEncode a.1,rawNoteEncode mu.1)
    (∀ E i : Nat, terminalEntryScanWith f p = some (some (E,i)) ↔
      FirstEntry f a.1.repr mu.1.repr i ∧ E = entryNormAt f a.1.repr i) ∧
    (terminalEntryScanWith f p = some none ↔
      ∀ i : Nat, ¬ FirstEntry f a.1.repr mu.1.repr i)) ∧
  ∀ (f : Nat → Nat) (a : NONote),
    terminalEntryScanWith f (rawNoteEncode a.1,0) = some (some (terminalWith f a.1.repr))

/-- Closed entry hit/miss foundation only. No fixed-endpoint lift,
source affordability policy, or actual finite-strip substitution. -/
def FullTerminalEntryScan : Prop :=
  TerminalEntryScanGuardExact ∧ BoundedTerminalEntryIndexExact ∧
    TerminalEntryScanEffective ∧ TerminalEntryScanActual

end Targets
end LogicLineages.PermittedControl
