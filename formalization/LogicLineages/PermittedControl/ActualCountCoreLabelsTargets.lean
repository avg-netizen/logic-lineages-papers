module
public import LogicLineages.PermittedControl.ActualZeroClassReplacementTargets
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountCoreLabels
open OrdinalComparison FieldComparison PreparedProjection
open SelectedCountOnlyClass (omegaSquareNote prefixTarget)

inductive Shape where
  | invalid
  | shortCount (k : Nat)
  | identityPrefix
  | properPrefix (target : NONote)

/-- Use the original proper guard at its own exact norm to check only
shape, not affordability at a real input. Tags 0/1/2/3 are invalid,
short original count, identity prefix, and strict proper prefix. -/
def rawTag (lam mu : Nat) : Nat :=
  if closedProperEntryGuard (lam,mu,rawNormCode lam) then
    if shortGapLengthCode lam mu = 0 then
      let eta := ordinalAddCode mu (rawNoteEncode omegaSquareNote.1)
      if rawComparisonCode eta lam = 1 then 2
      else if rawComparisonCode eta lam = 0 then 3 else 0
    else 1
  else 0

def classify (lam mu : NONote) : Shape :=
  match rawTag (rawNoteEncode lam.1) (rawNoteEncode mu.1) with
  | 1 => .shortCount (shortGapLength lam mu)
  | 2 => .identityPrefix
  | 3 => .properPrefix (prefixTarget mu)
  | _ => .invalid

/-- A full value label denotes f(q), not the actual signed count k.
No ordinary parameter is emitted for an invalid or short count. -/
def fieldLabel (lam mu : NONote) : Option ValueField :=
  match classify lam mu with
  | .identityPrefix => some (.iterate 1)
  | .properPrefix eta => some (.entry 1 lam eta)
  | _ => none

def rawLabel (lam mu : Nat) : Option LongFieldCode :=
  match rawTag lam mu with
  | 2 => some (0,1,0,0)
  | 3 => some (1,1,lam,ordinalAddCode mu (rawNoteEncode omegaSquareNote.1))
  | _ => none

def ExactCountCoreClassifier : Prop :=
  ∀ lam mu : NONote,
    let eta := prefixTarget mu
    let proper := ProperField (.entry 0 lam mu)
    let k := shortGapLength lam mu
    (¬ proper → classify lam mu = .invalid) ∧
    (proper → 0 < k → classify lam mu = .shortCount k) ∧
    (proper → k = 0 → eta.1.repr = lam.1.repr → classify lam mu = .identityPrefix) ∧
    (proper → k = 0 → eta.1.repr < lam.1.repr → classify lam mu = .properPrefix eta) ∧
    (proper → k = 0 → lam.1.repr < eta.1.repr → classify lam mu = .invalid) ∧
    rawLabel (rawNoteEncode lam.1) (rawNoteEncode mu.1) = (fieldLabel lam mu).map longFieldCode

def ExactShortCountHasNoCoreLabel : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (rank : Nat) (lam mu : NONote),
    ProperField (.entry 0 lam mu) → actualOrdinalNorm lam.1.repr ≤ ρ rank →
      let k := shortGapLength lam mu
      0 < k →
      classify lam mu = .shortCount k ∧ fieldLabel lam mu = none ∧
      FirstEntry f (countInitial lam.1.repr (ρ rank)) mu.1.repr k ∧
      lowerOperandRead f ρ (.count rank lam mu) = some (some k)

/-- Both readers are on the original raw coordinate. The identity
prefix goes through the genuine bare fixed-entry scan, which permits
the equality case; only strict prefixes become a proper ordinary field. -/
def ExactPaidLongCountCoreLabel : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (rank : Nat) (lam mu : NONote),
    LongField (.entry 0 lam mu) →
    max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr + 3) ≤ ρ rank →
    let eta := prefixTarget mu
    let x := ρ rank
    let A := countInitial lam.1.repr x
    ∃ (F : ValueField) (i k q : Nat),
      fieldLabel lam mu = some F ∧
      (eta.1.repr < lam.1.repr →
        classify lam mu = .properPrefix eta ∧ F = .entry 1 lam eta ∧ 0 < i) ∧
      (eta.1.repr = lam.1.repr →
        classify lam mu = .identityPrefix ∧ F = .iterate 1 ∧ i = 0) ∧
      eta.1.repr ≤ lam.1.repr ∧
      FirstEntry f A eta.1.repr i ∧ FirstEntry f A mu.1.repr k ∧
      q = entryNormAt f A i ∧ q = f^[i] x ∧
      fixedEntryClosedScan f (rawNoteEncode lam.1,rawNoteEncode eta.1,x) = some (some (q,i)) ∧
      lowerOperandRead f ρ (.count rank lam mu) = some (some k) ∧
      ProperField F ∧ LowerOperandActual f ρ (.ordinary rank F) (f q) ∧
      lowerOperandRead f ρ (.ordinary rank F) = some (some (f q)) ∧
      2 * (k : Int) = (f q : Int) + 2 * (i : Int) + 2 * Targets.countCoreConstant mu.1.repr

def FullActualCountCoreLabels : Prop :=
  ExactCountCoreClassifier ∧ ExactShortCountHasNoCoreLabel ∧ ExactPaidLongCountCoreLabel

end LogicLineages.PermittedControl.ActualCountCoreLabels
