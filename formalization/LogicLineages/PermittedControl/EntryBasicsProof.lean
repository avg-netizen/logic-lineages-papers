module
public import LogicLineages.PermittedControl.EntryTargets
public import LogicLineages.PermittedControl.EncodedEvaluatorProof
public import LogicLineages.PermittedControl.FunnelProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem interval_tail (a nu : Ordinal.{0}) (hlo : nu ≤ a) (hhi : a < nu + Ordinal.omega0) :
    ∃ n : Nat, a = nu + (n : Ordinal) := by
  have hd : a - nu < Ordinal.omega0 := by
    apply (add_lt_add_iff_left nu).mp
    rwa [Ordinal.add_sub_cancel_of_le hlo]
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hd
  exact ⟨n, by rw [← hn]; exact (Ordinal.add_sub_cancel_of_le hlo).symm⟩

theorem limitPart_finite (n : Nat) : actualLimitPart (n : Ordinal.{0}) = 0 := by
  simp [actualLimitPart, Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n)]

theorem interval_iff_limitPart (a nu : Ordinal.{0}) (hnu : nu = 0 ∨ Order.IsSuccLimit nu) :
    (nu ≤ a ∧ a < nu + Ordinal.omega0) ↔ actualLimitPart a = nu := by
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨n, rfl⟩ := interval_tail a nu hlo hhi
    rcases hnu with rfl | hnu
    · simpa using limitPart_finite n
    · exact limitPart_tail nu hnu n
  · intro h
    have ht : (actualTailPart a : Ordinal) = a % Ordinal.omega0 := by
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt a Ordinal.omega0_ne_zero)
      simp only [actualTailPart, hn, Ordinal.card_nat, Cardinal.toNat_natCast]
    have he : a = nu + (actualTailPart a : Ordinal) := by
      rw [ht, ← h]
      exact (Ordinal.div_add_mod a Ordinal.omega0).symm
    rw [he]
    exact ⟨le_self_add, (add_lt_add_iff_left nu).mpr (Ordinal.natCast_lt_omega0 _)⟩

theorem descent_finite (f : Nat → Nat) (n : Nat) : descentWith f (n : Ordinal.{0}) = 0 := by
  classical
  unfold descentWith
  rw [limitPart_finite]
  simp [actualMaximumPredecessor, actualBoundedPredecessors]

theorem actual_after_terminal_finite (f : Nat → Nat) (a : Ordinal.{0}) (ha : a < epsilonZero)
    (k : Nat) (hk : (terminalWith f a).2 ≤ k) : (descentWith f)^[k] a < Ordinal.omega0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  rw [Nat.add_comm (terminalWith f a).2 r, Function.iterate_add_apply, (terminal_firstFinite f a ha).1]
  induction r with
  | zero => exact Ordinal.natCast_lt_omega0 _
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ih
    rw [hn, descent_finite]
    exact Ordinal.omega0_pos

theorem encoded_after_terminal_fixed (f : Nat → Nat) (a : NONote) (k : Nat)
    (hk : (terminalWith f a.1.repr).2 ≤ k) :
    encodedStatesWith f (rawNoteEncode a.1) k =
      encodedStatesWith f (rawNoteEncode a.1) (terminalWith f a.1.repr).2 := by
  let D := (terminalWith f a.1.repr).2
  have htraj := trajectory_correct f a D le_rfl
  let z : NONote := ⟨rawNoteDecode (encodedStatesWith f (rawNoteEncode a.1) D), htraj.1⟩
  have hz : z.1.repr < Ordinal.omega0 := by
    rw [htraj.2, (terminal_firstFinite f a.1.repr (normalRepresentationSound a)).1]
    exact Ordinal.natCast_lt_omega0 _
  have ht := (encodedFiniteCorrect z).1.mpr hz
  rw [rawNoteEncodeDecode] at ht
  have hfix : encodedStepWith f (encodedStatesWith f (rawNoteEncode a.1) D) =
      encodedStatesWith f (rawNoteEncode a.1) D := by simp [encodedStepWith, ht]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  change (encodedStepWith f)^[D + r] (rawNoteEncode a.1) = _
  rw [Nat.add_comm D r, Function.iterate_add_apply]
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih]; exact hfix

theorem firstEntry_le_terminal (f : Nat → Nat) (a nu : Ordinal.{0}) (ha : a < epsilonZero)
    (hnu : nu = 0 ∨ Order.IsSuccLimit nu) (i : Nat) (hi : FirstEntry f a nu i) :
    i ≤ (terminalWith f a).2 := by
  by_contra hn
  have hlt : (terminalWith f a).2 < i := by omega
  have hfin := actual_after_terminal_finite f a ha i (by omega)
  rcases hnu with rfl | hnu
  · apply hi.2.2 _ hlt
    exact ⟨zero_le, by simpa using actual_after_terminal_finite f a ha (terminalWith f a).2 le_rfl⟩
  · exact (not_lt_of_ge ((Ordinal.omega0_le_of_isSuccLimit hnu).trans hi.1)) hfin

end LogicLineages.PermittedControl
