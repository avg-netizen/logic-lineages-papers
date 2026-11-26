module
public import LogicLineages.PermittedControl.FixedEntryClosedScanTargets
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- The two checked normal-limit guards together validate the raw endpoint
shapes. Strict order makes the left endpoint nonzero. Affordability is
the source inequality at the given coordinate, not a solver-tail bound. -/
def closedProperEntryGuard (p : FixedEntryClosedArgs) : Bool :=
  terminalScanGuard (p.1,p.2.1) && terminalScanGuard (p.2.1,p.1) &&
    decide (rawComparisonCode p.2.1 p.1 = 0 ∧ rawNormCode p.1 ≤ p.2.2)

/-- Invalid endpoints or an unaffordable source input are rejected, not
reported as a valid skipped target in the actual descent. -/
noncomputable def closedProperEntryResult (f : Nat → Nat) (p : FixedEntryClosedArgs) :
    TerminalEntryScanResult :=
  if closedProperEntryGuard p then fixedEntryClosedScan f p else none

abbrev ClosedNaturalFieldResult := Option (Option Nat)

/-- Ordinary value field on its actual, unchanged input x. A proper
entry hit applies the original outer iterate to its norm. Neither
miss nor rejection becomes a numerical field value. -/
noncomputable def closedOrdinaryValueField (f : Nat → Nat) (P : LongFieldCode) (x : Nat) :
    ClosedNaturalFieldResult :=
  let (tag,a,lam,mu) := P
  if tag = 0 then some (some (f^[a] x))
  else (closedProperEntryResult f (lam,mu,x)).map
    (fun r => r.map (fun hit => f^[a] hit.1))

/-- Count of the very same proper entry, using its actual first-hit
index rather than a count inferred from its value. -/
noncomputable def closedOrdinaryCountField (f : Nat → Nat) (p : FixedEntryClosedArgs) :
    ClosedNaturalFieldResult :=
  (closedProperEntryResult f p).map (fun r => r.map Prod.snd)

def ClosedOrdinaryValueDomain (F : ValueField) (x : Nat) : Prop :=
  match F with
  | .iterate _ => True
  | .entry a lam mu => ProperField (.entry a lam mu) ∧ actualOrdinalNorm lam.1.repr ≤ x

def DecodedClosedProperEntryDomain (p : FixedEntryClosedArgs) : Prop :=
  let lam := rawNoteDecode p.1
  let mu := rawNoteDecode p.2.1
  ONote.NF lam ∧ ONote.NF mu ∧ Order.IsSuccLimit lam.repr ∧
    (mu.repr = 0 ∨ Order.IsSuccLimit mu.repr) ∧ mu.repr < lam.repr ∧
    actualOrdinalNorm lam.repr ≤ p.2.2

def ClosedProperEntryDomainExact : Prop :=
  Primrec closedProperEntryGuard ∧
  (∀ p : FixedEntryClosedArgs, closedProperEntryGuard p = true ↔ DecodedClosedProperEntryDomain p) ∧
  ∀ (lam mu : NONote) (x : Nat),
    closedProperEntryGuard (rawNoteEncode lam.1,rawNoteEncode mu.1,x) = true ↔
      ClosedOrdinaryValueDomain (.entry 0 lam mu) x

def ClosedOrdinaryFieldEffective : Prop :=
  ∀ (f : Nat → Nat), Computable f →
    Computable (closedProperEntryResult f) ∧
    Computable₂ (closedOrdinaryValueField f) ∧
    Computable (closedOrdinaryCountField f)

def ClosedProperEntryResultExact : Prop :=
  (∀ (f : Nat → Nat) (p : FixedEntryClosedArgs),
    closedProperEntryResult f p = none ↔ ¬DecodedClosedProperEntryDomain p) ∧
  ∀ (f : Nat → Nat) (lam mu : NONote) (x : Nat),
    ClosedOrdinaryValueDomain (.entry 0 lam mu) x →
    let R := closedProperEntryResult f (rawNoteEncode lam.1,rawNoteEncode mu.1,x)
    let A := countInitial lam.1.repr x
    (∀ E i : Nat, R = some (some (E,i)) ↔
      FirstEntry f A mu.1.repr i ∧ E = entryNormAt f A i) ∧
    (R = some none ↔ ∀ i : Nat, ¬FirstEntry f A mu.1.repr i)

def ClosedOrdinaryValueActual : Prop :=
  ∀ (f : Nat → Nat) (F : ValueField) (x : Nat),
    let R := closedOrdinaryValueField f (longFieldCode F) x
    (R = none ↔ ¬ClosedOrdinaryValueDomain F x) ∧
    (ClosedOrdinaryValueDomain F x →
      (∀ v : Nat, R = some (some v) ↔ FieldValue f F x v) ∧
      (R = some none ↔ ∀ v : Nat, ¬FieldValue f F x v))

def ClosedOrdinaryCountActual : Prop :=
  ∀ (f : Nat → Nat) (lam mu : NONote) (x : Nat),
    let R := closedOrdinaryCountField f (rawNoteEncode lam.1,rawNoteEncode mu.1,x)
    let A := countInitial lam.1.repr x
    let D := ClosedOrdinaryValueDomain (.entry 0 lam mu) x
    (R = none ↔ ¬D) ∧
    (D →
      (∀ i : Nat, R = some (some i) ↔ FirstEntry f A mu.1.repr i) ∧
      (R = some none ↔ ∀ i : Nat, ¬FirstEntry f A mu.1.repr i))

/-- One-coordinate closed value/count suppliers. Identity and strip
substitution are separately scoped, not encoded as proper intervals. -/
def FullClosedOrdinaryFieldEvaluation : Prop :=
  ClosedProperEntryDomainExact ∧ ClosedOrdinaryFieldEffective ∧
    ClosedProperEntryResultExact ∧ ClosedOrdinaryValueActual ∧ ClosedOrdinaryCountActual

end LogicLineages.PermittedControl.FieldComparison
