module
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessor

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualDivisiblePrefixMaximum : Targets.ActualDivisiblePrefixMaximum := by
  intro k r hk hr hrpos e hmin hbound b hbudget
  have hdiv : Ordinal.omega0 ^ e ∣ k := (actualMinExponentDivisibility k hk e).mp hmin
  have hsource := actualDivisiblePrefixNormAddition k r hk hr e hdiv hbound
  let m := actualMaximumPredecessor r (b - actualOrdinalNorm k)
  have hm := actualMaximumPredecessor_correct r hrpos hr (b - actualOrdinalNorm k)
  have hmε : m < epsilonZero := hm.1.1.trans hr
  have hout := actualDivisiblePrefixNormAddition k m hk hmε e hdiv (hm.1.1.trans hbound)
  have hpos : 0 < k + r := hrpos.trans_le le_add_self
  apply Eq.symm
  apply actualMaximumPredecessor_unique (k + r) hpos hsource.1 b (k + m)
  refine ⟨⟨add_lt_add_right hm.1.1 k, ?_⟩, ?_⟩
  · have hn := hout.2
    have hmb : actualOrdinalNorm m ≤ b - actualOrdinalNorm k := hm.1.2
    omega
  · intro x hx
    have hxb : actualOrdinalNorm x ≤ b := hx.2
    by_cases hlow : x < k
    · exact (hlow.trans_le le_self_add).le
    · have hkx : k ≤ x := le_of_not_gt hlow
      have hx' : k + (x - k) < k + r := (Ordinal.add_sub_cancel_of_le hkx).trans_lt hx.1
      have hdelta : x - k < r := (add_lt_add_iff_left k).mp hx'
      have hdnorm := (actualDivisiblePrefixNormAddition k (x - k) hk
        (hdelta.trans hr) e hdiv (hdelta.trans hbound)).2
      rw [Ordinal.add_sub_cancel_of_le hkx] at hdnorm
      have hdbudget : actualOrdinalNorm (x - k) ≤ b - actualOrdinalNorm k := by omega
      have hdm : x - k ≤ m := hm.2 ⟨hdelta, hdbudget⟩
      rw [← Ordinal.add_sub_cancel_of_le hkx]
      exact add_le_add_right hdm k

theorem actualCompatiblePrefixMaximum : Targets.ActualCompatiblePrefixMaximum := by
  intro k r hk hr hlimit hcompat b hbudget
  obtain ⟨rn, hrn⟩ := normalRepresentationComplete r hr
  rcases rn with ⟨raw, hnf⟩
  cases raw with
  | zero =>
    have hpos := hlimit.bot_lt
    rw [← hrn] at hpos
    change 0 < 0 at hpos
    exact False.elim ((not_lt_of_ge (le_refl 0)) hpos)
  | oadd f c t =>
    have hc : ((c : Nat) : Ordinal) ≠ 0 := by exact_mod_cast c.ne_zero
    have hcnf : Ordinal.CNF Ordinal.omega0 (ONote.oadd f c t).repr =
        (f.repr, ((c : Nat) : Ordinal)) :: Ordinal.CNF Ordinal.omega0 t.repr :=
      Ordinal.CNF.opow_mul_add Ordinal.one_lt_omega0 hc
        (Ordinal.natCast_lt_omega0 _) hnf.snd'.repr_lt
    have hhead : (f.repr, ((c : Nat) : Ordinal)) ∈ Ordinal.CNF Ordinal.omega0 r := by
      rw [← hrn, hcnf]
      exact List.mem_cons_self
    have hmin : actualMinExponentAtLeast k f.repr := fun p hp => hcompat p hp _ hhead
    have hbound : r < Ordinal.omega0 ^ (f.repr + 1) := by
      rw [← hrn]
      exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 _) hnf.snd'.repr_lt
        (Order.lt_add_one_iff.mpr le_rfl)
    exact actualDivisiblePrefixMaximum k r hk hr hlimit.bot_lt f.repr hmin hbound b hbudget

end LogicLineages.OrdinalComparison
