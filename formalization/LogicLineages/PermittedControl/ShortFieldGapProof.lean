module
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem encode_injective : Function.Injective rawNoteEncode := by
  intro a b h
  have hd := congrArg rawNoteDecode h
  have ha : rawNoteDecode (rawNoteEncode a) = a := rawNoteDecodeEncode a
  have hb : rawNoteDecode (rawNoteEncode b) = b := rawNoteDecodeEncode b
  rw [ha,hb] at hd
  exact hd

private theorem parse_positive_iff (o : ONote) (k : Nat) (hk : 0 < k) :
    rawShortGapLength (rawNoteEncode o) = k ↔ o = ONote.oadd (NONote.ofNat 1).1 ⟨k,hk⟩ ONote.zero := by
  constructor
  · intro h
    cases o with
    | zero => exact False.elim (Nat.ne_of_gt hk h.symm)
    | oadd e c t =>
      have hc : (c : Nat) - 1 + 1 = c := Nat.sub_add_cancel c.pos
      simp only [rawNoteEncode, rawShortGapLength, Nat.unpair_pair] at h
      split at h
      · rename_i hs
        have he : e = (NONote.ofNat 1).1 := encode_injective hs.1
        have ht : t = ONote.zero := encode_injective hs.2
        have hcoe : c = (⟨k,hk⟩ : {n : Nat // 0 < n}) := Subtype.ext (hc.symm.trans h)
        rw [he,hcoe,ht]
      · exact False.elim (Nat.ne_of_gt hk h.symm)
  · intro h
    rw [h]
    simp [rawNoteEncode, rawShortGapLength, Nat.unpair_pair, Nat.sub_add_cancel hk]

private theorem shortMonomial_repr (k : Nat) (hk : 0 < k) :
    (ONote.oadd (NONote.ofNat 1).1 ⟨k,hk⟩ ONote.zero).repr = Ordinal.omega0 * (k : Ordinal) := by
  change Ordinal.omega0 ^ (ONote.ofNat 1).repr * (k : Ordinal) + 0 = _
  rw [ONote.repr_ofNat, Nat.cast_one, Ordinal.opow_one, add_zero]

theorem shortGapRecognition : ShortGapRecognition := by
  intro lam mu hp k hk
  have hle : mu.1.repr ≤ lam.1.repr := hp.2.2.le
  have hsyntax : shortGapLength lam mu = k ↔
      (lam-mu).1 = ONote.oadd (NONote.ofNat 1).1 ⟨k,hk⟩ ONote.zero := by
    unfold shortGapLength shortGapLengthCode
    rw [ordinal_sub_note_code]
    exact parse_positive_iff _ k hk
  have hrepr : (lam-mu).1 = ONote.oadd (NONote.ofNat 1).1 ⟨k,hk⟩ ONote.zero ↔
      lam.1.repr-mu.1.repr = Ordinal.omega0 * (k : Ordinal) := by
    letI : ONote.NF (ONote.oadd (NONote.ofNat 1).1 ⟨k,hk⟩ ONote.zero) :=
      ONote.NF.oadd (inferInstance : ONote.NF (NONote.ofNat 1).1) ⟨k,hk⟩ ONote.NFBelow.zero
    simpa only [note_sub_repr, shortMonomial_repr] using
      (ONote.repr_inj (a := (lam-mu).1) (b := ONote.oadd (NONote.ofNat 1).1 ⟨k,hk⟩ ONote.zero)).symm
  have hadd := Ordinal.add_sub_cancel_of_le hle
  have hends : lam.1.repr-mu.1.repr = Ordinal.omega0 * (k : Ordinal) ↔
      lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal) := by
    constructor
    · intro h
      rw [← h, hadd]
    · intro h
      exact add_left_cancel (hadd.trans h)
  exact ⟨hsyntax,hsyntax.trans hrepr,(hsyntax.trans hrepr).trans hends⟩

end LogicLineages.PermittedControl.FieldComparison
