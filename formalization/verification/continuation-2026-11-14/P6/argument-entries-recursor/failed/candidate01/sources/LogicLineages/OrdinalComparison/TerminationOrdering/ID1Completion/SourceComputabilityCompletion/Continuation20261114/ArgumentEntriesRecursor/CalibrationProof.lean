module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.RawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.CalibrationProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RawProof

theorem nonCons (n : Nat) (c : Code (Fin n)) (h : tagValue (codeNumber c) ≠ 7)
    (hs : ArgumentEntriesLayer.semanticStep c none = NumberedExchangeCode.argumentEntries c) :
    rawValue (codeNumber c) = Encodable.encode (NumberedExchangeCode.argumentEntries c) := by
  rw [rawValueEquation,if_neg h]
  have hn := ArgumentEntriesLayer.NativeProof.nativeStep n c none
  rw [hs] at hn
  exact hn

theorem valueOnCode (n : Nat) (c : Code (Fin n)) :
    rawValue (codeNumber c) = Encodable.encode (NumberedExchangeCode.argumentEntries c) := by
  induction c with
  | var i => exact nonCons n (.var i) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | lam tau q ih => exact nonCons n (.lam tau q) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | app tau q a ihq iha => exact nonCons n (.app tau q a) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | bottom tau => exact nonCons n (.bottom tau) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | ordinary h base ih => exact nonCons n (.ordinary h base) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | numbered k h tau base ts extras ihb ihe =>
    exact nonCons n (.numbered k h tau base ts extras) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | argumentsNil => exact nonCons n (.argumentsNil) (by simp [tagValue,codeNumber,Nat.unpair_pair]) rfl
  | argumentsCons tau q rest ihq ihr =>
    rw [rawValueEquation]
    have ht : tagValue (codeNumber (Code.argumentsCons tau q rest)) = 7 := by
      simp [tagValue,codeNumber,Nat.unpair_pair]
    have hs : secondValue (codeNumber (Code.argumentsCons tau q rest)) = codeNumber rest := by
      simp [secondValue,tagValue,payloadValue,codeNumber,Nat.unpair_pair]
    rw [if_pos ht,hs,ihr]
    exact ArgumentEntriesLayer.NativeProof.nativeStep n (.argumentsCons tau q rest)
      (NumberedExchangeCode.argumentEntries rest)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.CalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.CalibrationProof
