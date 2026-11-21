module
public import LogicLineages.PermittedControl.TerminalEntryScanTargets
public import LogicLineages.PermittedControl.FixedEntryProgramTargets

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Original fixed entry input order: raw lambda, raw target, natural t. -/
abbrev FixedEntryClosedArgs := Nat × Nat × Nat

/-- Use the source's literal initial state, not a searched representative. -/
def fixedEntryClosedStartTarget (p : FixedEntryClosedArgs) : Nat × Nat :=
  (canonicalInitialCode p.1 p.2.2,p.2.1)

/-- The separate raw-lambda guard is essential: an invalid source note is
not an admitted start, even if a numeric operation returns a normal note. -/
def fixedEntryClosedProgram (f : Nat → Nat) (p : FixedEntryClosedArgs) : Part TerminalEntryScanResult :=
  if rawNormalCode p.1 = 1 then terminalEntryScanProgram f (fixedEntryClosedStartTarget p)
  else Part.some none

/-- The definite realization has certified domain. Its representation's
fallback is never taken, by the independent all-input Dom clause. -/
noncomputable def fixedEntryClosedScan (f : Nat → Nat) (p : FixedEntryClosedArgs) :
    TerminalEntryScanResult := by
  classical
  exact (fixedEntryClosedProgram f p).getOrElse none

namespace Targets

def FixedEntryClosedEffective : Prop :=
  Primrec fixedEntryClosedStartTarget ∧
  ∀ f : Nat → Nat,
    (∀ p : FixedEntryClosedArgs, (fixedEntryClosedProgram f p).Dom) ∧
    (Computable f → Partrec (fixedEntryClosedProgram f) ∧ Computable (fixedEntryClosedScan f))

def FixedEntryClosedRawExact : Prop :=
  (∀ (f : Nat → Nat) (p : FixedEntryClosedArgs),
    rawNormalCode p.1 = 1 →
      fixedEntryClosedScan f p = terminalEntryScanWith f (fixedEntryClosedStartTarget p)) ∧
  ∀ (f : Nat → Nat) (p : FixedEntryClosedArgs),
    fixedEntryClosedScan f p = none ↔
      ¬(ONote.NF (rawNoteDecode p.1) ∧ ONote.NF (rawNoteDecode p.2.1) ∧
        ((rawNoteDecode p.2.1).repr = 0 ∨ Order.IsSuccLimit (rawNoteDecode p.2.1).repr))

/-- All natural t, with the actual countInitial convention. This target
neither requires nor asserts source affordability of a call at t. -/
def FixedEntryClosedActual : Prop :=
  ∀ (f : Nat → Nat) (lam mu : NONote) (t : Nat),
    (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) →
    let p := (rawNoteEncode lam.1,rawNoteEncode mu.1,t)
    let A := countInitial lam.1.repr t
    (∀ E i : Nat, fixedEntryClosedScan f p = some (some (E,i)) ↔
      FirstEntry f A mu.1.repr i ∧ E = entryNormAt f A i) ∧
    (fixedEntryClosedScan f p = some none ↔ ∀ i : Nat, ¬ FirstEntry f A mu.1.repr i)

def FixedEntryClosedOriginalGraph : Prop :=
  ∀ (f : Nat → Nat), Computable f →
  ∀ (lam mu : NONote) (t E i : Nat),
    (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) →
    let p := (rawNoteEncode lam.1,rawNoteEncode mu.1,t)
    fixedEntryClosedScan f p = some (some (E,i)) ↔ (E,i) ∈ fixedEntryProgram f p

/-- Fixed-entry hit/miss supplier; no source guard/identity specialization,
ordinary-field/count evaluation or finite-strip substitution. -/
def FullFixedEntryClosedScan : Prop :=
  FixedEntryClosedEffective ∧ FixedEntryClosedRawExact ∧
    FixedEntryClosedActual ∧ FixedEntryClosedOriginalGraph

end Targets
end LogicLineages.PermittedControl
