module
public import LogicLineages.PermittedControl.EqualGapCertificateDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

def EqualGapCertificateEffective : Prop :=
  Primrec (fun p : Nat×Nat×Nat => equalGapCertificateCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Nat×Nat => equalGapCertificateTailCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  ∀ mu nu delta : Nat, equalGapCertificateCode mu nu delta ≤ 2

/-- Actual equal-gap comparison for arbitrary finite tails and original
clocks. No supplied hit, divergence, phase or affordability hypothesis. -/
def ActualEqualGapCertificate : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu delta : NONote) (A A' : Ordinal.{0}) (t : Nat),
  (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) →
  (nu.1.repr=0 ∨ Order.IsSuccLimit nu.1.repr) → Order.IsSuccLimit delta.1.repr →
  A < epsilonZero → A' < epsilonZero →
  equalGapCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1) B ≤ t →
  actualLimitPart A=mu.1.repr+delta.1.repr → actualLimitPart A'=nu.1.repr+delta.1.repr →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  ∃ tau sigma : Nat, FirstEntry f A mu.1.repr tau ∧ FirstEntry f A' nu.1.repr sigma ∧
    entryNormAt f A tau=f^[tau] t ∧ entryNormAt f A' sigma=f^[sigma] t ∧
    numericalComparison (entryNormAt f A tau) (entryNormAt f A' sigma)=
      equalGapCertificateCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1)

/-- Source bound-only tail trichotomy on actual canonical entry maps. The
fixed computed sign decides every tail input; all canonical normalization
and target affordability are conclusions of the proof, not premises. -/
def EqualGapSourceTail : Prop := ∀ (mu nu delta : NONote),
  (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) →
  (nu.1.repr=0 ∨ Order.IsSuccLimit nu.1.repr) → Order.IsSuccLimit delta.1.repr →
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B → ∀ t : Nat,
  equalGapCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1) B ≤ t →
  let A := countInitial (mu.1.repr+delta.1.repr) t
  let A' := countInitial (nu.1.repr+delta.1.repr) t
  let sign := equalGapCertificateCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1)
  ∃ tau sigma : Nat, FirstEntry f A mu.1.repr tau ∧ FirstEntry f A' nu.1.repr sigma ∧
    (sign=0 → entryNormAt f A tau < entryNormAt f A' sigma) ∧
    (sign=1 → entryNormAt f A tau = entryNormAt f A' sigma) ∧
    (sign=2 → entryNormAt f A' sigma < entryNormAt f A tau)

/-- Full source prop:equal-gap: real algorithm/tail and actual source order,
including identity. No later inverse-threshold or field-comparison credit. -/
def FullEqualGapCertificate : Prop :=
  EqualGapCertificateEffective ∧ ActualEqualGapCertificate ∧ EqualGapSourceTail

end LogicLineages.PermittedControl.Targets
