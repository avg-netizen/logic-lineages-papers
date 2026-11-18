module
public import LogicLineages.PermittedControl.OrdinalEndpointCodeDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual all-input algorithm, not a choice of a semantic normal representative. -/
def OrdinalEndpointCodeEffective : Prop :=
  Primrec₂ ordinalAddCode ∧ Primrec₂ ordinalSubCode

/-- Literal agreement even for raw, non-normal syntax with the installed
Mathlib recursive notation algorithms. -/
def OrdinalEndpointCodeLiteral : Prop := ∀ a b : Nat,
  ordinalAddCode a b=rawNoteEncode (rawNoteDecode a+rawNoteDecode b) ∧
  ordinalSubCode a b=rawNoteEncode (rawNoteDecode a-rawNoteDecode b)

/-- Normal-domain correctness for ordinary addition and left subtraction,
including normality of the produced code and both actual ordinal equalities. -/
def OrdinalEndpointCodeSemantic : Prop := ∀ a b : NONote,
  let ac := rawNoteEncode a.1
  let bc := rawNoteEncode b.1
  ONote.NF (rawNoteDecode (ordinalAddCode ac bc)) ∧
  ONote.NF (rawNoteDecode (ordinalSubCode ac bc)) ∧
  (rawNoteDecode (ordinalAddCode ac bc)).repr=a.1.repr+b.1.repr ∧
  (rawNoteDecode (ordinalSubCode ac bc)).repr=a.1.repr-b.1.repr

/-- Supporting endpoint-computation foundation only; no inverse-table or
translated/offset threshold assembly is hidden in this contract. -/
def OrdinalEndpointCodeFoundation : Prop :=
  OrdinalEndpointCodeEffective ∧ OrdinalEndpointCodeLiteral ∧ OrdinalEndpointCodeSemantic

end LogicLineages.PermittedControl.Targets
