module
public import LogicLineages.PermittedControl.FixedEntryProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

def CanonicalInitialCodeCorrect : Prop := Primrec₂ canonicalInitialCode ∧
  ∀ (lambda : NONote) (t : Nat),
    ONote.NF (rawNoteDecode (canonicalInitialCode (rawNoteEncode lambda.1) t)) ∧
    (rawNoteDecode (canonicalInitialCode (rawNoteEncode lambda.1) t)).repr=countInitial lambda.1.repr t

def FixedEntryProgramEffectivity : Prop := ∀ f : Nat → Nat, Computable f →
  Partrec (fixedEntryProgram f) ∧
  ∀ (lambda mu : NONote) (t E i : Nat), (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) →
    ((E,i) ∈ fixedEntryProgram f (rawNoteEncode lambda.1,rawNoteEncode mu.1,t) ↔
      FirstEntry f (countInitial lambda.1.repr t) mu.1.repr i ∧
      E=entryNormAt f (countInitial lambda.1.repr t) i)

/-- Actual on-tail domain and witnessed result, including target zero.
No successful hit or computation premise is provided. -/
def FixedEntryProgramTail : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lambda mu : NONote) (t : Nat), Order.IsSuccLimit lambda.1.repr →
    (mu.1.repr=0 ∨ Order.IsSuccLimit mu.1.repr) → mu.1.repr<lambda.1.repr →
    max 2 (max (actualOrdinalNorm lambda.1.repr) (actualOrdinalNorm mu.1.repr))≤t →
    (fixedEntryProgram f (rawNoteEncode lambda.1,rawNoteEncode mu.1,t)).Dom ∧
    ∃ i E : Nat, (E,i) ∈ fixedEntryProgram f (rawNoteEncode lambda.1,rawNoteEncode mu.1,t) ∧
      FirstEntry f (countInitial lambda.1.repr t) mu.1.repr i ∧ E=f^[i] t

def FixedEntryProgramFoundation : Prop := CanonicalInitialCodeCorrect ∧
  FixedEntryProgramEffectivity ∧ FixedEntryProgramTail

end LogicLineages.PermittedControl.Targets
