module
public import LogicLineages.OrdinalComparison.CompatiblePrefixTargets
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
public import LogicLineages.OrdinalComparison.Control

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem raw_min_exponent_divisibility (a : ONote) (ha : ONote.NF a) (e : Ordinal) :
    actualMinExponentAtLeast a.repr e ↔ Ordinal.omega0 ^ e ∣ a.repr := by
  induction a with
  | zero => simp [actualMinExponentAtLeast, ONote.repr]
  | oadd f c t ihf iht =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd f c t).repr =
        (f.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) ha.snd'.repr_lt
    have hmin : actualMinExponentAtLeast (ONote.oadd f c t).repr e ↔
        e ≤ f.repr ∧ actualMinExponentAtLeast t.repr e := by
      unfold actualMinExponentAtLeast
      rw [hcnf]
      constructor
      · intro h
        exact ⟨h _ (List.mem_cons_self), fun p hp => h p (List.mem_cons_of_mem _ hp)⟩
      · rintro ⟨hf, ht⟩ p hp
        rcases List.mem_cons.mp hp with hp | hp
        · subst p
          exact hf
        · exact ht p hp
    rw [hmin]
    constructor
    · rintro ⟨hf, ht⟩
      have hlead : Ordinal.omega0 ^ e ∣ Ordinal.omega0 ^ f.repr * ((c : Nat) : Ordinal) :=
        (Ordinal.opow_dvd_opow Ordinal.omega0 hf).mul_right _
      exact (Ordinal.dvd_add_iff hlead).mpr ((iht ha.snd).mp ht)
    · intro hd
      have h := ha.of_dvd_omega0_opow hd
      exact ⟨h.1, (iht ha.snd).mpr h.2⟩

theorem actualMinExponentDivisibility : Targets.ActualMinExponentDivisibility := by
  intro k hk e
  obtain ⟨kn, hkn⟩ := normalRepresentationComplete k hk
  rw [← hkn]
  exact raw_min_exponent_divisibility kn.1 kn.2 e

private theorem phi_shift_bound (c n : Nat) : c + Phi n ≤ Phi (c + n) := by
  induction c with
  | zero => simp only [Nat.zero_add, le_refl]
  | succ c ih =>
    have h := Phi_strictMono (show c + n < (c + 1) + n by omega)
    omega

theorem compensatedPrefixControlBounds : Targets.CompensatedPrefixControlBounds := by
  intro c
  constructor
  · intro n n' h
    exact Nat.sub_le_sub_right (Phi_strictMono.monotone (Nat.add_le_add_left h c)) c
  · intro n
    have hshift := phi_shift_bound c n
    have hbound : Phi n ≤ compensatedPrefixControl c n := by
      unfold compensatedPrefixControl
      omega
    exact ⟨hbound, (self_lt_Phi n).trans_le hbound⟩

end LogicLineages.OrdinalComparison
