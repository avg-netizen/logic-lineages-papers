module
public import LogicLineages.PermittedControl.PureCertificateDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual raw program effectivity, including its explicit tail, on every
natural input, not just normal codes. -/
def PureCertificateEffective : Prop :=
  Primrec (fun p : Nat×Nat×Nat => pureCertificateCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Nat×Nat => pureCertificateTailCode p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Complete actual pure-phase comparison, including E=1, E=2 and zero
targets. Every phase admission, visit, budget, hit and clock must be derived. -/
def ActualPureCertificate : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (mu nu E : NONote) (A A' : Ordinal.{0}) (t : Nat),
  (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) →
  (nu.1.repr=0 ∨ Order.IsSuccLimit nu.1.repr) → 1 ≤ E.1.repr →
  A < epsilonZero → A' < epsilonZero →
  pureCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1) B ≤ t →
  actualLimitPart A=mu.1.repr+Ordinal.omega0^E.1.repr →
  actualLimitPart A'=nu.1.repr+Ordinal.omega0^E.1.repr →
  actualOrdinalNorm A=t → actualOrdinalNorm A'=t →
  ∃ tau sigma : Nat, FirstEntry f A mu.1.repr tau ∧ FirstEntry f A' nu.1.repr sigma ∧
    entryNormAt f A tau=f^[tau] t ∧ entryNormAt f A' sigma=f^[sigma] t ∧
    numericalComparison (entryNormAt f A tau) (entryNormAt f A' sigma)=
      pureCertificateCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1)

def PureCertificateFoundation : Prop := PureCertificateEffective ∧ ActualPureCertificate

end LogicLineages.PermittedControl.Targets
