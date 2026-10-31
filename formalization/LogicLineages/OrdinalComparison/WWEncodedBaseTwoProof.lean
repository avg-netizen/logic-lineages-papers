module
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoTargets
public import LogicLineages.OrdinalComparison.RawNotationCode
@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem sub_zero_raw (t : ONote) : ONote.sub t (0 : ONote) = t := by cases t <;> simp [ONote.sub, ← ONote.zero_def]

theorem rawSubtractOneCodeCorrect : Targets.RawSubtractOneCodeCorrect := by
  intro a
  cases a with
  | zero => rfl
  | oadd e c t =>
    change rawSubtractOneCode (rawNoteEncode (.oadd e c t)) =
      rawNoteEncode (ONote.sub (.oadd e c t) (.oadd .zero 1 .zero))
    cases e with
    | oadd f d u => simp [rawSubtractOneCode, rawNoteEncode, ONote.sub, ONote.cmp]
    | zero =>
      rcases c with ⟨c, hc⟩
      cases c with
      | zero => omega
      | succ k =>
        cases k with
        | zero => simp [rawSubtractOneCode, rawNoteEncode, ONote.sub, ONote.cmp, sub_zero_raw]
        | succ k => simp [rawSubtractOneCode, rawNoteEncode, ONote.sub, ONote.cmp, Nat.succPNat]

theorem rawSubtractOneCodePrimitiveRecursive : Targets.RawSubtractOneCodePrimitiveRecursive := by
  have hp := Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  have he := Primrec.fst.comp hp
  have hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hp))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hp))
  have hnode := Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.nat_sub.comp hc (Primrec.const 1)) ht))
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp he (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp hc (Primrec.const 0)) ht hnode) Primrec.id)

private theorem encode_zero_iff (e : ONote) : rawNoteEncode e = 0 ↔ e = .zero := by
  cases e <;> simp [rawNoteEncode]

theorem rawSplitPrimeCodeCorrect : Targets.RawSplitPrimeCodeCorrect := by
  intro a
  induction a with
  | zero =>
    simp [rawNoteEncode, rawSplitPrimeCode, ONote.split', ← ONote.zero_def]
    decide
  | oadd e c t ihe iht =>
    by_cases he : e = .zero
    · subst e
      simp [rawNoteEncode, rawSplitPrimeCode, ONote.split', Nat.sub_add_cancel c.pos]
    · have hec : rawNoteEncode e ≠ 0 := (encode_zero_iff e).not.mpr he
      have he0 : e ≠ (0 : ONote) := by simpa only [← ONote.zero_def] using he
      simp only [rawNoteEncode, rawSplitPrimeCode, Nat.unpair_pair, hec, if_false,
        ONote.split', he0, iht]
      rw [rawSubtractOneCodeCorrect e]

theorem rawSplitPrimeCodePrimitiveRecursive : Targets.RawSplitPrimeCodePrimitiveRecursive := by
  let tailCode : Nat → Nat := fun n => n.pred.unpair.2.unpair.2
  let children : Nat → List Nat := fun n => if n = 0 then [] else [tailCode n]
  let assemble : Nat → List Nat → Option Nat := fun n rs => some
    (if n = 0 then 0 else
      let e := n.pred.unpair.1
      let c := n.pred.unpair.2.unpair.1
      if e = 0 then Nat.pair 0 (c+1) else
        Nat.pair (Nat.pair (rawSubtractOneCode e) (Nat.pair c rs.head!.unpair.1)+1) rs.head!.unpair.2)
  have hfields : Primrec (fun n : Nat => n.pred.unpair) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  have ht : Primrec tailCode := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp hfields))
  have hchildren : Primrec children := Primrec.ite
    (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const [])
    (Primrec.list_cons.comp ht (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hf := hfields.comp (Primrec.fst : Primrec (fun p : Nat × List Nat => p.1))
    have he := Primrec.fst.comp hf
    have hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp hf))
    have hrs := Primrec.unpair.comp (Primrec.list_headI.comp (Primrec.snd : Primrec (fun p : Nat × List Nat => p.2)))
    have hnode := Primrec.succ.comp (Primrec₂.natPair.comp
      (rawSubtractOneCodePrimitiveRecursive.comp he)
      (Primrec₂.natPair.comp hc (Primrec.fst.comp hrs)))
    exact Primrec.option_some.comp (Primrec.ite
      (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp he (Primrec.const 0))
        (Primrec₂.natPair.comp (Primrec.const 0) (Primrec.succ.comp hc))
        (Primrec₂.natPair.comp hnode (Primrec.snd.comp hrs))))
  apply Primrec.nat_omega_rec' rawSplitPrimeCode Primrec.id hchildren ha
  · intro n t ht
    cases n with
    | zero => simp [children] at ht
    | succ n =>
      have he : t = n.unpair.2.unpair.2 := by simpa [children, tailCode] using ht
      subst t
      exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n))
  · intro n
    cases n with
    | zero => simp [assemble, children, rawSplitPrimeCode]
    | succ n => simp [assemble, children, tailCode, rawSplitPrimeCode]

theorem encodedBaseTwoPowerCorrect : Targets.EncodedBaseTwoPowerCorrect := by
  intro a
  letI : ONote.NF a.1 := a.2
  rcases hs : ONote.split' a.1 with ⟨b, k⟩
  have hsplit := ONote.nf_repr_split' hs
  let c : ℕ+ := ⟨2 ^ k, Nat.pow_pos (by omega)⟩
  let z : NONote := ⟨.oadd b c .zero, ONote.NF.oadd hsplit.1 c ONote.NFBelow.zero⟩
  have hzcode : encodedBaseTwoPower (rawNoteEncode a.1) = rawNoteEncode z.1 := by
    rw [encodedBaseTwoPower, rawSplitPrimeCodeCorrect, hs]
    simp [z, c, rawNoteEncode]
  have hpower : (2 : Ordinal) ^ a.1.repr = Ordinal.omega0 ^ b.repr * ((2 ^ k : Nat) : Ordinal) := by
    rw [hsplit.2, Ordinal.opow_add, Ordinal.opow_mul,
      Ordinal.opow_omega0 (a := (2 : Ordinal))
        (by exact_mod_cast (show (1 : Nat) < 2 by omega))
        (by simpa using Ordinal.natCast_lt_omega0 2)]
    congr 1
    simpa only [Ordinal.opow_natCast, Nat.cast_ofNat] using (Ordinal.natCast_pow 2 k).symm
  have hz : z.1.repr = (2 : Ordinal) ^ a.1.repr := by
    rw [hpower]
    simp [z, c, ONote.repr]
  let p := NONote.opow ⟨ONote.ofNat 2, ONote.nf_ofNat 2⟩ a
  have hp : p.1.repr = (2 : Ordinal) ^ a.1.repr := by
    change ((ONote.ofNat 2) ^ a.1).repr = _
    rw [ONote.repr_opow, ONote.repr_ofNat]
    rfl
  letI : ONote.NF z.1 := z.2
  letI : ONote.NF p.1 := p.2
  rw [hzcode]
  exact congrArg rawNoteEncode (ONote.repr_inj.mp (hz.trans hp.symm))

private theorem pow_two_primitive : Primrec (fun k : Nat => 2 ^ k) := by
  have h := Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, pow_succ]

theorem encodedBaseTwoPowerPrimitiveRecursive : Targets.EncodedBaseTwoPowerPrimitiveRecursive := by
  have hp := Primrec.unpair.comp rawSplitPrimeCodePrimitiveRecursive
  exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.fst.comp hp)
    (Primrec₂.natPair.comp
      (Primrec.nat_sub.comp (pow_two_primitive.comp (Primrec.snd.comp hp)) (Primrec.const 1))
      (Primrec.const 0)))
end LogicLineages.OrdinalComparison
