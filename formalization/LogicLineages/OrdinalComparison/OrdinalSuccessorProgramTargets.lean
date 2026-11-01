module
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def OrdinalSuccessorProgramsPrimitiveRecursive : Prop :=
  Primrec encodedOrdinalFiniteRemainder ∧ Primrec encodedOrdinalSuccessorPredecessor

/-- Genuine uniformly computed ordinary predecessor, exact source successor
identity and exact additive norm drop; no predecessor/normality/norm oracle. -/
def ActualOrdinalSuccessorPredecessorProgram : Prop :=
  ∀ eta : NONote, 0<encodedOrdinalFiniteRemainder (rawNoteEncode eta.1) →
    ∃ pred : NONote,
      encodedOrdinalSuccessorPredecessor (rawNoteEncode eta.1)=rawNoteEncode pred.1 ∧
      eta.1.repr=pred.1.repr+1 ∧ Vendor.R1.treeWeight eta.1=Vendor.R1.treeWeight pred.1+1

/-- The actual source stop branch: no positive finite remainder means zero
or an ordinal limit. Positive remainder is exactly the successor case. -/
def ActualOrdinalFiniteRemainderClassification : Prop :=
  ∀ eta : NONote, encodedOrdinalFiniteRemainder (rawNoteEncode eta.1)=0 ↔
    eta.1.repr=0 ∨ Order.IsSuccLimit eta.1.repr

/-- Successor normalization of a higher exponent never jumps below the
opposite exponent, with the SAME actual compiled predecessor. -/
def ActualOrdinalSuccessorNoJump : Prop :=
  ∀ eta lower : NONote, lower.1.repr<eta.1.repr →
    0<encodedOrdinalFiniteRemainder (rawNoteEncode eta.1) →
    ∃ pred : NONote,
      encodedOrdinalSuccessorPredecessor (rawNoteEncode eta.1)=rawNoteEncode pred.1 ∧
      eta.1.repr=pred.1.repr+1 ∧ lower.1.repr≤pred.1.repr ∧
      Vendor.R1.treeWeight eta.1=Vendor.R1.treeWeight pred.1+1

end LogicLineages.OrdinalComparison.Targets
