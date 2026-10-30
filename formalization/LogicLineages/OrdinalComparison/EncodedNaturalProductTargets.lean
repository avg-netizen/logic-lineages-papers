module
public import LogicLineages.OrdinalComparison.EncodedNaturalProductDefinitions
public import LogicLineages.OrdinalComparison.NaturalProduct
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent remaining natural-product effectiveness clause of source
paper05 lem:finite-balls. The literal monomial helper and whole product must
agree with the accepted source algorithms on all raw inputs. Full source
normality, independent actual ordinal denotation and expanded-tree norm bound
are retained; no abstract natural-product correctness supplier is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def EncodedMonomialProductCorrect : Prop :=
  ∀ (e b : ONote) (c : ℕ+),
    encodedMonomialProduct (rawNoteEncode e) ((c : Nat) - 1) (rawNoteEncode b) =
      rawNoteEncode (rawMonomialProduct e c b)

def EncodedMonomialProductPrimitiveRecursive : Prop :=
  Primrec (fun p : (Nat × Nat) × Nat => encodedMonomialProduct p.1.1 p.1.2 p.2)

def EncodedNaturalProductCorrect : Prop :=
  ∀ a b : ONote,
    encodedNaturalProduct (rawNoteEncode a) (rawNoteEncode b) = rawNoteEncode (rawNaturalProduct a b)

def EncodedNaturalProductPrimitiveRecursive : Prop := Primrec₂ encodedNaturalProduct

def EncodedNaturalProductSourceCorrect : Prop :=
  ∀ a b : NONote,
    let result := rawNoteDecode (encodedNaturalProduct (rawNoteEncode a.1) (rawNoteEncode b.1))
    ONote.NF result ∧ result.repr = ordinalNaturalProduct a.1.repr b.1.repr ∧
      Vendor.R1.treeWeight result ≤ Vendor.R1.treeWeight a.1 * Vendor.R1.treeWeight b.1

end LogicLineages.OrdinalComparison.Targets
