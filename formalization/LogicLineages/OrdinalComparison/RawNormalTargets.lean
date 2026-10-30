module
public import LogicLineages.OrdinalComparison.RawNormalDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent literal NF-recognition supplier for the paper 05 finite-balls
algorithm. These targets use the accepted rawNote codec and the original NF
class, including rejection of arbitrary nonnormal raw inputs. No alternative
normality relation is substituted for Mathlib's hereditary CNF condition. -/

namespace LogicLineages.OrdinalComparison.Targets

def RawNormalDecodeCorrect : Prop :=
  ∀ n : Nat, rawNormalCode n = 1 ↔ ONote.NF (rawNoteDecode n)

def RawNormalCorrect : Prop :=
  ∀ a : ONote, rawNormalCode (rawNoteEncode a) = 1 ↔ ONote.NF a

def RawNormalPrimitiveRecursive : Prop := Nat.Primrec rawNormalCode

end LogicLineages.OrdinalComparison.Targets
