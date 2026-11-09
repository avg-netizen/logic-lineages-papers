module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecProof
open TermCodec

private theorem decode_step (payload tag : Nat) (htag : tag < 10) :
    decode (10 * payload + tag) =
      if tag = 0 then .numeral payload
      else if tag = 1 then .variable payload
      else if tag = 2 then .add (decode payload.unpair.1) (decode payload.unpair.2)
      else if tag = 3 then .subtract (decode payload.unpair.1) (decode payload.unpair.2)
      else if tag = 4 then .multiply payload.unpair.1 (decode payload.unpair.2)
      else if tag = 5 then .divide payload.unpair.1 (decode payload.unpair.2)
      else if tag = 6 then .phi (decode payload)
      else if tag = 7 then .hyper (decode payload)
      else if tag = 8 then .phiInverse (decode payload)
      else .hyperInverse (decode payload) := by
  have hm : (10 * payload + tag) % 10 = tag := by omega
  have hd : (10 * payload + tag) / 10 = payload := by omega
  rw [decode, hm, hd]

theorem literalTermRoundTrip : TermCodecTargets.LiteralTermRoundTrip := by
  intro t
  induction t with
  | numeral n =>
    change decode (10 * n + 0) = .numeral n
    rw [decode_step n 0 (by decide)]
    rfl
  | «variable» i =>
    rw [Term.encode, decode_step i 1 (by decide)]
    rfl
  | add a b iha ihb =>
    rw [Term.encode, decode_step _ 2 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, iha, ihb]
  | subtract a b iha ihb =>
    rw [Term.encode, decode_step _ 3 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, iha, ihb]
  | multiply c a ih =>
    rw [Term.encode, decode_step _ 4 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, ih]
  | divide c a ih =>
    rw [Term.encode, decode_step _ 5 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, ih]
  | phi a ih =>
    rw [Term.encode, decode_step _ 6 (by decide)]
    simp only [reduceIte, ih]
  | hyper a ih =>
    rw [Term.encode, decode_step _ 7 (by decide)]
    simp only [reduceIte, ih]
  | phiInverse a ih =>
    rw [Term.encode, decode_step _ 8 (by decide)]
    simp only [reduceIte, ih]
  | hyperInverse a ih =>
    rw [Term.encode, decode_step _ 9 (by decide)]
    simp only [reduceIte, ih]

theorem everyOriginalCodeRoundTrip : TermCodecTargets.EveryOriginalCodeRoundTrip := by
  intro code
  induction code using Nat.strong_induction_on with
  | h code ih =>
    have htag : code % 10 < 10 := Nat.mod_lt code (by decide)
    rw [decode]
    split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 h8
    · simp only [Term.encode]; omega
    · simp only [Term.encode]; omega
    all_goals
      have hpos : 0 < code := by omega
      have hd : code / 10 < code := Nat.div_lt_self hpos (by decide)
      have hq := ih (code / 10) hd
      have hl := ih (code / 10).unpair.1 (lt_of_le_of_lt (Nat.unpair_left_le _) hd)
      have hr := ih (code / 10).unpair.2 (lt_of_le_of_lt (Nat.unpair_right_le _) hd)
      simp only [Term.encode, hq, hl, hr, Nat.pair_unpair]
      omega

theorem originalEncodeInjectivity : TermCodecTargets.OriginalEncodeInjectivity := by
  intro a b hab
  calc
    a = decode a.encode := (literalTermRoundTrip a).symm
    _ = decode b.encode := congrArg decode hab
    _ = b := literalTermRoundTrip b

/-- The exact original encoding, with its proved total inverse. -/
def originalEquiv : Term ≃ Nat :=
  ⟨Term.encode, decode, literalTermRoundTrip, everyOriginalCodeRoundTrip⟩

def originalCoding : Primcodable Term := Primcodable.ofEquiv Nat originalEquiv

theorem literalPrimitiveCoding : TermCodecTargets.LiteralPrimitiveCoding :=
  ⟨originalCoding, fun _ => rfl⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecProof
