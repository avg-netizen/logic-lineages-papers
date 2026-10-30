module
public import LogicLineages.OrdinalComparison.EncodedNaturalSumDefinitions
public import LogicLineages.OrdinalComparison.NaturalSum
public import LogicLineages.OrdinalComparison.NaturalArithmeticDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent remaining natural-sum effectiveness clause of source paper05
lem:finite-balls. Correctness is the accepted literal sorted-CNF merge on every
raw input. The full source gate additionally retains normality, actual ordinal
natural-sum denotation and additive expanded-tree norm on normal inputs. -/

namespace LogicLineages.OrdinalComparison.Targets

def EncodedNaturalSumCorrect : Prop :=
  ∀ a b : ONote,
    encodedNaturalSum (rawNoteEncode a) (rawNoteEncode b) = rawNoteEncode (rawNaturalSum a b)

def EncodedNaturalSumPrimitiveRecursive : Prop := Primrec₂ encodedNaturalSum

def EncodedNaturalSumSourceCorrect : Prop :=
  ∀ a b : NONote,
    let result := rawNoteDecode (encodedNaturalSum (rawNoteEncode a.1) (rawNoteEncode b.1))
    ONote.NF result ∧ result.repr = ordinalNaturalSum a.1.repr b.1.repr ∧
      Vendor.R1.treeWeight result = Vendor.R1.treeWeight a.1 + Vendor.R1.treeWeight b.1

end LogicLineages.OrdinalComparison.Targets
