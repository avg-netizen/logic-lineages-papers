module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseRecursionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricActualCollapse.Proof

theorem natural_facts (n : Nat) :
    (n : Ordinal) < epsilonZero ∧ actualOrdinalNorm (n : Ordinal) = n := by
  have hs := normalRepresentationSound (NONote.ofNat n)
  have hn := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
  rw [norm_ofNat] at hn
  change (ONote.ofNat n).repr < epsilonZero at hs
  change actualOrdinalNorm (ONote.ofNat n).repr = n at hn
  rw [ONote.repr_ofNat] at hs hn
  exact ⟨hs,hn⟩

theorem finiteValues : Targets.FiniteValues := by
  intro G hG n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      apply Nat.le_antisymm
      · apply (equation G (n : Ordinal) (natural_facts n).1).2
        intro b hb _
        obtain ⟨k,rfl⟩ := Ordinal.lt_omega0.mp (hb.trans (Ordinal.natCast_lt_omega0 n))
        have hk : k < n := by exact_mod_cast hb
        rw [ih k hk]
        omega
      · cases n with
        | zero => exact Nat.zero_le _
        | succ n =>
            have hn : (n : Ordinal) < ((n+1 : Nat) : Ordinal) := by exact_mod_cast Nat.lt_succ_self n
            have hnorm : actualOrdinalNorm (n : Ordinal) ≤
                G (actualOrdinalNorm ((n+1 : Nat) : Ordinal)) := by
              rw [(natural_facts n).2,(natural_facts (n+1)).2]
              exact (Nat.le_succ n).trans (hG (n+1))
            have hc := (equation G ((n+1 : Nat) : Ordinal) (natural_facts (n+1)).1).1
              (n : Ordinal) hn hnorm
            rw [ih n (Nat.lt_succ_self n)] at hc
            exact hc
end LogicLineages.OrdinalComparison.ParametricActualCollapse.Proof
