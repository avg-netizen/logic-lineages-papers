module
public import LogicLineages.OrdinalComparison.RawNotationCodeTargets
public import LogicLineages.OrdinalComparison.RawNotationComputabilityTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem rawNoteEncodeEquation : Targets.RawNoteEncodeEquation := by
  exact ⟨rfl, fun _ _ _ => rfl⟩

theorem rawNoteDecodeEquation : Targets.RawNoteDecodeEquation := by
  constructor
  · rw [rawNoteDecode]
  · intro n
    rw [rawNoteDecode]

theorem rawNoteDecodeEncode : Targets.RawNoteDecodeEncode := by
  intro a
  induction a with
  | zero => rw [rawNoteEncode, rawNoteDecode]
  | oadd e c t ihe iht =>
      rw [rawNoteEncode, rawNoteDecode]
      simp only [Nat.unpair_pair, ihe, iht]
      congr 1
      apply Subtype.ext
      exact Nat.sub_add_cancel c.pos

theorem rawNoteEncodeDecode : Targets.RawNoteEncodeDecode := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => rw [rawNoteDecode, rawNoteEncode]
      | succ n =>
          rw [rawNoteDecode, rawNoteEncode]
          change Nat.pair (rawNoteEncode (rawNoteDecode n.unpair.1))
            (Nat.pair (n.unpair.2.unpair.1 + 1 - 1)
              (rawNoteEncode (rawNoteDecode n.unpair.2.unpair.2))) + 1 = n + 1
          rw [Nat.add_sub_cancel,
            ih n.unpair.1 (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
            ih n.unpair.2.unpair.2
              (Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n))),
            Nat.pair_unpair, Nat.pair_unpair]

theorem rawNoteNormalizationPrimitiveRecursive : Targets.RawNoteNormalizationPrimitiveRecursive := by
  apply Nat.Primrec.succ.of_eq
  intro n
  rw [rawNoteEncodeDecode n]

/-- Explicit codec structure; deliberately not installed as a global instance. -/
def rawONoteDenumerable : Denumerable ONote where
  encode := rawNoteEncode
  decode n := some (rawNoteDecode n)
  encodek a := congrArg some (rawNoteDecodeEncode a)
  decode_inv n := ⟨rawNoteDecode n, rfl, rawNoteEncodeDecode n⟩

/-- The normalization certificate is primitive recursive because every raw
natural code is valid and both roundtrips have been proved. This does not
certify any ordinal operation or normality predicate. -/
def rawONotePrimcodable : Primcodable ONote := by
  letI : Denumerable ONote := rawONoteDenumerable
  exact Primcodable.ofDenumerable ONote

theorem rawNoteDenumerableFaithful : Targets.RawNoteDenumerableFaithful rawONoteDenumerable :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem rawNotePrimcodableFaithful : Targets.RawNotePrimcodableFaithful rawONotePrimcodable :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end LogicLineages.OrdinalComparison
