module
public import LogicLineages.PermittedControl.FieldComparisonTargets
public import LogicLineages.PermittedControl.OrdinalEndpointCodeTargets
public import LogicLineages.OrdinalComparison.RawNormCodeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- Decode the single literal monomial `ω * k` in the raw tree code:
one exponent, positive coefficient, zero remainder. Zero signals no match. -/
def rawShortGapLength : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if n.unpair.1 = rawNoteEncode (NONote.ofNat 1).1 ∧ n.unpair.2.unpair.2 = 0
      then n.unpair.2.unpair.1 + 1 else 0

def shortGapLengthCode (lam mu : Nat) : Nat :=
  rawShortGapLength (ordinalSubCode lam mu)

def shortGapLength (lam mu : NONote) : Nat :=
  shortGapLengthCode (rawNoteEncode lam.1) (rawNoteEncode mu.1)

/-- Zero means unchanged; a positive result codes the replacement iterate
exponent plus one. The caller retains the endpoints in the unchanged case. -/
def shortIterateCode (lam mu a : Nat) : Nat :=
  let k := shortGapLengthCode lam mu
  if k = 0 then 0 else a + k + 1

def normalizeShortField : ValueField → ValueField
  | .iterate a => .iterate a
  | .entry a lam mu =>
      match shortIterateCode (rawNoteEncode lam.1) (rawNoteEncode mu.1) a with
      | 0 => .entry a lam mu
      | n + 1 => .iterate n

def shortFieldTailCode (lam mu B : Nat) : Nat :=
  max (rawNormCode lam) (max (rawNormCode mu + 3) (max 1 B))

def shortFieldTail (B : Nat) : ValueField → Nat
  | .iterate _ => 0
  | .entry _ lam mu => shortFieldTailCode (rawNoteEncode lam.1) (rawNoteEncode mu.1) B

/-- Literal canonical syntax, actual gap, and actual endpoint equation all
agree, with the coefficient fully recovered. No finite search limit. -/
def ShortGapRecognition : Prop :=
  ∀ lam mu : NONote, ProperField (.entry 0 lam mu) →
  ∀ (k : Nat) (hk : 0 < k),
    (shortGapLength lam mu = k ↔
      (lam - mu).1 = ONote.oadd (NONote.ofNat 1).1 ⟨k, hk⟩ ONote.zero) ∧
    (shortGapLength lam mu = k ↔
      lam.1.repr - mu.1.repr = Ordinal.omega0 * (k : Ordinal)) ∧
    (shortGapLength lam mu = k ↔
      lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal))

/-- Raw classifiers and tail are uniform, including on all natural codes;
semantic calibration is only on the proper NONote domain. -/
def ShortFieldPreprocessingEffective : Prop :=
  Primrec rawShortGapLength ∧ Primrec₂ shortGapLengthCode ∧
  Primrec (fun p : Nat × Nat × Nat => shortIterateCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat => shortFieldTailCode p.1 p.2.1 p.2.2) ∧
  ∀ (lam mu : NONote) (B : Nat),
    shortFieldTail B (.entry 0 lam mu) =
      max (actualOrdinalNorm lam.1.repr) (max (actualOrdinalNorm mu.1.repr + 3) (max 1 B))

def ShortFieldNormalization : Prop :=
  (∀ a : Nat, normalizeShortField (.iterate a) = .iterate a) ∧
  (∀ (a : Nat) (lam mu : NONote), ProperField (.entry a lam mu) →
    let k := shortGapLength lam mu
    (k = 0 → LongField (.entry a lam mu) ∧
      normalizeShortField (.entry a lam mu) = .entry a lam mu) ∧
    (0 < k → normalizeShortField (.entry a lam mu) = .iterate (a + k))) ∧
  (∀ F : ValueField, ProperField F → LongField (normalizeShortField F)) ∧
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ F : ValueField, ProperField F → ∀ x v : Nat, shortFieldTail B F ≤ x →
      (FieldValue f F x v ↔ FieldValue f (normalizeShortField F) x v)

/-- Supporting preprocessing only, not the printed field-comparison lemma. -/
def FullShortFieldPreprocessing : Prop :=
  ShortGapRecognition ∧ ShortFieldPreprocessingEffective ∧ ShortFieldNormalization

end LogicLineages.PermittedControl.FieldComparison
