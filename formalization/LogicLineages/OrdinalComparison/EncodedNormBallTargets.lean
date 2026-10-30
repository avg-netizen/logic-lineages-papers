module
public import LogicLineages.OrdinalComparison.EncodedNormBallDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent encoded enumeration supplier for paper 05 lem:finite-balls.
Completeness is required on every raw notation and every natural code. The
accepted source norm and NF predicates remain the actual mathematical tests.
This alone does not claim natural-sum/product effectiveness or closed-collapse
evaluation, the other distinct source obligations. -/

namespace LogicLineages.OrdinalComparison.Targets

def RawNormCodeBoundCorrect : Prop :=
  ∀ (b : Nat) (a : ONote), Vendor.R1.treeWeight a ≤ b → rawNoteEncode a ≤ rawNormCodeBound b

def EncodedNormalNormBallCorrect : Prop :=
  ∀ (b : Nat) (a : ONote),
    rawNoteEncode a ∈ encodedNormalNormBall b ↔ ONote.NF a ∧ Vendor.R1.treeWeight a ≤ b

def EncodedNormalNormBallDecodeCorrect : Prop :=
  ∀ b n : Nat,
    n ∈ encodedNormalNormBall b ↔ ONote.NF (rawNoteDecode n) ∧
      Vendor.R1.treeWeight (rawNoteDecode n) ≤ b

def EncodedNormalNormBallPrimitiveRecursive : Prop := Primrec encodedNormalNormBall

end LogicLineages.OrdinalComparison.Targets
