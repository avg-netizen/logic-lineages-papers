module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecProof
open CommonLayerSyntax SourceFormulaCodec

private theorem term_roundtrip (t : BaseTerm) : BaseTerm.decode t.encode = t :=
  CommonLayerSyntax.Proof.baseRoundtrip t

private theorem decode_step (a tag : Nat) (ht : tag < 5) :
    decode (5 * a + tag) =
      if tag = 0 then .equal (BaseTerm.decode a.unpair.1) (BaseTerm.decode a.unpair.2)
      else if tag = 1 then .less (BaseTerm.decode a.unpair.1) (BaseTerm.decode a.unpair.2)
      else if tag = 2 then .negative (decode a)
      else if tag = 3 then .conjunction (decode a.unpair.1) (decode a.unpair.2)
      else .existsNat a.unpair.1 (decode a.unpair.2) := by
  have hm : (5 * a + tag) % 5 = tag := by omega
  have hd : (5 * a + tag) / 5 = a := by omega
  rw [decode, hm, hd]

theorem sourceRoundtrip : SourceFormulaCodecTargets.SourceRoundtrip := by
  intro p
  induction p with
  | equal a b =>
      simpa [SourceFormula.encode, Nat.unpair_pair, term_roundtrip] using
        decode_step (Nat.pair a.encode b.encode) 0 (by decide)
  | less a b =>
      simpa [SourceFormula.encode, Nat.unpair_pair, term_roundtrip] using
        decode_step (Nat.pair a.encode b.encode) 1 (by decide)
  | negative p ih =>
      simpa [SourceFormula.encode, ih] using decode_step p.encode 2 (by decide)
  | conjunction p q ihp ihq =>
      simpa [SourceFormula.encode, Nat.unpair_pair, ihp, ihq] using
        decode_step (Nat.pair p.encode q.encode) 3 (by decide)
  | existsNat i p ih =>
      simpa [SourceFormula.encode, Nat.unpair_pair, ih] using
        decode_step (Nat.pair i p.encode) 4 (by decide)

theorem codeRoundtrip : SourceFormulaCodecTargets.CodeRoundtrip := by
  intro code
  induction code using Nat.strong_induction_on with
  | h code ih =>
      rw [decode]
      split_ifs with h0 h1 h2 h3
      · change 5 * Nat.pair (BaseTerm.decode (code / 5).unpair.1).encode
          (BaseTerm.decode (code / 5).unpair.2).encode = code
        rw [CommonLayerProgram.Proof.base_code_roundtrip, CommonLayerProgram.Proof.base_code_roundtrip, Nat.pair_unpair]
        omega
      · change 5 * Nat.pair (BaseTerm.decode (code / 5).unpair.1).encode
          (BaseTerm.decode (code / 5).unpair.2).encode + 1 = code
        rw [CommonLayerProgram.Proof.base_code_roundtrip, CommonLayerProgram.Proof.base_code_roundtrip, Nat.pair_unpair]
        omega
      · have hn : 0 < code := by omega
        have hd : code / 5 < code := Nat.div_lt_self hn (by decide)
        change 5 * (decode (code / 5)).encode + 2 = code
        rw [ih _ hd]
        omega
      · have hn : 0 < code := by omega
        have hd : code / 5 < code := Nat.div_lt_self hn (by decide)
        have hl : (code / 5).unpair.1 < code := lt_of_le_of_lt (Nat.unpair_left_le _) hd
        have hr : (code / 5).unpair.2 < code := lt_of_le_of_lt (Nat.unpair_right_le _) hd
        change 5 * Nat.pair (decode (code / 5).unpair.1).encode (decode (code / 5).unpair.2).encode + 3 = code
        rw [ih _ hl, ih _ hr, Nat.pair_unpair]
        omega
      · have hn : 0 < code := by omega
        have hd : code / 5 < code := Nat.div_lt_self hn (by decide)
        have hr : (code / 5).unpair.2 < code := lt_of_le_of_lt (Nat.unpair_right_le _) hd
        change 5 * Nat.pair (code / 5).unpair.1 (decode (code / 5).unpair.2).encode + 4 = code
        rw [ih _ hr, Nat.pair_unpair]
        omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecProof
