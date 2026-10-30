module
public import LogicLineages.OrdinalComparison.PolynomialOrdinalNormalProof
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem vector_eq_init_last (d : Nat) (a b : Fin (d + 1) → Nat)
    (hi : Fin.init a = Fin.init b) (hl : a (Fin.last d) = b (Fin.last d)) : a = b := by
  calc
    a = Fin.snoc (Fin.init a) (a (Fin.last d)) := (Fin.snoc_init_self a).symm
    _ = Fin.snoc (Fin.init b) (b (Fin.last d)) := by rw [hi, hl]
    _ = b := Fin.snoc_init_self b

private theorem zero_top_cannot_match (d : Nat) (a b : Fin (d + 1) → Nat)
    (ha : a (Fin.last d) = 0) (hb : b (Fin.last d) ≠ 0)
    (h : polynomialRawNote (d + 1) a = polynomialRawNote (d + 1) b) : False := by
  simp only [polynomialRawNote, dif_pos ha, dif_neg hb] at h
  have hr := congrArg ONote.repr h
  have hbelow := (polynomialRawNoteNormalBoundNorm d (Fin.init a)).2.1
  have hleading := ONote.omega0_le_oadd (ONote.ofNat d)
    (⟨b (Fin.last d), Nat.pos_of_ne_zero hb⟩ : PNat) (polynomialRawNote d (Fin.init b))
  rw [ONote.repr_ofNat, ← hr] at hleading
  exact (not_lt_of_ge hleading) hbelow

theorem polynomialRawNoteInjective : Targets.PolynomialRawNoteInjective := by
  intro d
  induction d with
  | zero =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | succ d ih =>
    intro a b h
    by_cases ha : a (Fin.last d) = 0
    · by_cases hb : b (Fin.last d) = 0
      · apply vector_eq_init_last d a b
        · apply ih
          simpa only [polynomialRawNote, dif_pos ha, dif_pos hb] using h
        · exact ha.trans hb.symm
      · exact False.elim (zero_top_cannot_match d a b ha hb h)
    · by_cases hb : b (Fin.last d) = 0
      · exact False.elim (zero_top_cannot_match d b a hb ha h.symm)
      · simp only [polynomialRawNote, dif_neg ha, dif_neg hb] at h
        have hparts := ONote.oadd.inj h
        exact vector_eq_init_last d a b (ih hparts.2.2)
          (congrArg (fun c : PNat => c.val) hparts.2.1)

theorem polynomialRawNoteOrdinalComplete : Targets.PolynomialRawNoteOrdinalComplete := by
  intro d
  induction d with
  | zero =>
    intro x hx
    have hz : x = 0 := Order.lt_one_iff.mp (by simpa only [Nat.cast_zero, Ordinal.opow_zero] using hx)
    exact ⟨fun i => Fin.elim0 i, hz.symm⟩
  | succ d ih =>
    intro x hx
    by_cases hsmall : x < Ordinal.omega0 ^ (d : Ordinal)
    · obtain ⟨a, ha⟩ := ih x hsmall
      refine ⟨Fin.snoc a 0, ?_⟩
      simpa [polynomialRawNote, Fin.snoc_last, Fin.init_snoc] using ha
    · have hexp : ((d + 1 : Nat) : Ordinal) < epsilonZero := by
        have h := normalRepresentationSound (NONote.ofNat (d + 1))
        change (ONote.ofNat (d + 1)).repr < epsilonZero at h
        rw [ONote.repr_ofNat] at h
        exact h
      have hpow : Ordinal.omega0 ^ ((d + 1 : Nat) : Ordinal) < epsilonZero :=
        (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr hexp
      obtain ⟨xn, hxn⟩ := normalRepresentationComplete x (hx.trans hpow)
      rcases xn with ⟨raw, hnf⟩
      cases raw with
      | zero =>
        apply False.elim
        apply hsmall
        rw [← hxn]
        exact Ordinal.opow_pos _ Ordinal.omega0_pos
      | oadd e c r =>
        have he : e.repr < ((d + 1 : Nat) : Ordinal) :=
          (ONote.NF.below_of_lt' (by rw [hxn]; exact hx) hnf).lt
        have hele : e.repr ≤ (d : Ordinal) := by
          rw [Nat.cast_add, Nat.cast_one] at he
          exact Order.lt_add_one_iff.mp he
        have hege : (d : Ordinal) ≤ e.repr := by
          by_contra hn
          have helt : e.repr < (d : Ordinal) := lt_of_not_ge hn
          apply hsmall
          rw [← hxn]
          exact (hnf.below_of_lt helt).repr_lt
        have heeq : e.repr = (d : Ordinal) := le_antisymm hele hege
        have hr : r.repr < Ordinal.omega0 ^ (d : Ordinal) := by
          rw [← heeq]
          exact hnf.snd'.repr_lt
        obtain ⟨a, ha⟩ := ih r.repr hr
        refine ⟨Fin.snoc a (c : Nat), ?_⟩
        simp only [polynomialRawNote, Fin.snoc_last, dif_neg c.ne_zero, Fin.init_snoc]
        change Ordinal.omega0 ^ (ONote.ofNat d).repr * ((c : Nat) : Ordinal) +
          (polynomialRawNote d a).repr = x
        rw [ONote.repr_ofNat, ha, ← heeq]
        exact hxn

end LogicLineages.OrdinalComparison
