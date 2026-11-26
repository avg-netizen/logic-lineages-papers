module
public import LogicLineages.PermittedControl.InitialCodeDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- All-code computation of the actual expanded list and joint predicate. -/
def InitialCodeEffective : Prop := Primrec originalUnitCodes ∧
  Primrec (fun p : Nat×Nat×Nat => initialPassCode p.1 p.2.1 p.2.2)

/-- Actual ordered CNF units, including all coefficient multiplicities, and
normality of every exponent code. No phase or list supplier is assumed. -/
def OriginalUnitCodeCorrect : Prop := ∀ delta : NONote,
  ((originalUnitCodes (rawNoteEncode delta.1)).map (fun n => (rawNoteDecode n).repr))=
    originalGapUnits delta.1.repr ∧
  ∀ n ∈ originalUnitCodes (rawNoteEncode delta.1), ONote.NF (rawNoteDecode n)

/-- Exact two original quadratic exceptions and parity, no-sensitive and
equal-leading-cost branches, on every positive actual limit gap. -/
def InitialPassCodeCorrect : Prop := ∀ mu nu delta : NONote,
  Order.IsSuccLimit delta.1.repr →
  (initialPassCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1)=true ↔
    initialPeelingPass mu.1.repr nu.1.repr delta.1.repr)

def InitialCodeFoundation : Prop := InitialCodeEffective ∧ OriginalUnitCodeCorrect ∧ InitialPassCodeCorrect

end LogicLineages.PermittedControl.Targets
