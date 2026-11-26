module
public import LogicLineages.PermittedControl.ThickArithmeticProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem phase_log_add_nat (P : Ordinal.{0}) (hP : 0 < P) (n : Nat) :
    Ordinal.log Ordinal.omega0 (P+(n : Ordinal)) = Ordinal.log Ordinal.omega0 P := by
  have hPb : P < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
  have hnb : (n : Ordinal) < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    (Ordinal.natCast_lt_omega0 n).trans_le (by
      simpa using (Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone
        (show (1 : Ordinal) ≤ Ordinal.log Ordinal.omega0 P+1 from le_add_self))
  have hb := Ordinal.isPrincipal_add_omega0_opow _ hPb hnb
  apply le_antisymm
  · exact Order.lt_add_one_iff.mp ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0
      (hP.trans_le le_self_add).ne').mp hb)
  · exact Ordinal.log_mono_right _ le_self_add

 theorem phase_limit_log (x : Ordinal.{0}) (hx : x < epsilonZero) (hn : Ordinal.omega0 ≤ x) :
    Ordinal.log Ordinal.omega0 x = Ordinal.log Ordinal.omega0 (actualLimitPart x) := by
  have hd := actualNonfiniteDecomposition x hn hx
  conv_lhs => rw [hd.2.2.1]
  exact phase_log_add_nat _ hd.2.1.bot_lt _

 theorem phase_limit_add (P x : Ordinal.{0}) (hx : x < epsilonZero) (hn : Ordinal.omega0 ≤ x) :
    actualLimitPart (P+x) = P+actualLimitPart x := by
  have hd := actualNonfiniteDecomposition x hn hx
  conv_lhs => rw [hd.2.2.1,← add_assoc]
  exact limitPart_tail _ (Ordinal.isSuccLimit_add P hd.2.1) _

 theorem resonant_local_separation (P a : Ordinal.{0}) (M X : Nat) (hP : P < epsilonZero)
    (ha : a < epsilonZero) (h2 : (2 : Ordinal) ≤ a)
    (hX : actualOrdinalNorm a+3 ≤ X) (hdiv : actualOrdinalNorm a ∣ M)
    (hmod : Int.ModEq (2*(M : Int)) (X : Int) (actualOrdinalNorm a : Int)) :
    actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^a) X) ≠
      actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^a) (X-1)) := by
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) h2
  have hpow := phase_power_below a ha
  have haNorm := thick_exponent_norm a ha h2
  rcases Ordinal.zero_or_succ_or_isSuccLimit a with hz | ⟨a0,ha0eq⟩ | hlim
  · subst a
    exact False.elim ((lt_irrefl 0) hapos)
  · subst a
    simp only [Order.succ_eq_add_one] at *
    have ha0 : a0 < epsilonZero := (show a0 < a0+1 from Order.lt_add_one_iff.mpr le_rfl).trans ha
    have hnorm : actualOrdinalNorm (a0+1) = 1+actualOrdinalNorm a0 := by
      have h := (actualFiniteTailClosureNorm a0 ha0 1).2
      simpa [Nat.add_comm] using h
    have ha0pos : 0 < a0 := by
      by_contra hn
      have hz : a0=0 := le_antisymm (le_of_not_gt hn) zero_le
      subst a0
      norm_num at h2
    let v := 1+actualOrdinalNorm a0
    have hv : 0 < v := by dsimp [v]; omega
    have hvX : v+3 ≤ X := by simpa only [hnorm] using hX
    have hdInt : (v : Int) ∣ 2*(M : Int) := by
      have hdv : v ∣ M := by simpa only [hnorm] using hdiv
      have hdNat : v ∣ 2*M := hdv.trans (dvd_mul_left M 2)
      exact_mod_cast hdNat
    have hr : Nat.ModEq v X v := Int.natCast_modEq_iff.mp (by
      simpa only [hnorm] using hmod.of_dvd hdInt)
    have hXdiv : v ∣ X := Nat.modEq_zero_iff_dvd.mp (hr.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
    have hz : X%v=0 := Nat.mod_eq_zero_of_dvd hXdiv
    have hmul : X/v*v=X := by simpa [hz, Nat.mul_comm] using Nat.div_add_mod X v
    have hquot : (X-1)/v < X/v := (Nat.div_lt_iff_lt_mul hv).mpr (by nlinarith [hmul])
    have hquotpos : 0 < X/v := Nat.div_pos (by omega) hv
    have htop := successorLocalTail a0 X ha0 (by omega)
    change actualMaximumPredecessor (Ordinal.omega0^(a0+1)) X =
      Ordinal.omega0^a0*((X/v : Nat) : Ordinal)+actualMaximumPredecessor (Ordinal.omega0^a0) (X%v) at htop
    rw [hz,actualOptimizedMaximumBaseCases.1 _ (Ordinal.opow_pos a0 Ordinal.omega0_pos)
      (phase_power_below a0 ha0),add_zero] at htop
    have hlow := successorLocalTail a0 (X-1) ha0 (by omega)
    have ht := (actualMaximumPredecessor_correct (Ordinal.omega0^a0)
      (Ordinal.opow_pos a0 Ordinal.omega0_pos) (phase_power_below a0 ha0) ((X-1)%v)).1.1
    have hlt : actualMaximumPredecessor (Ordinal.omega0^(a0+1)) (X-1) <
        Ordinal.omega0^a0*((X/v : Nat) : Ordinal) := by
      rw [hlow]
      exact Ordinal.opow_mul_add_lt_opow_mul ht (by exact_mod_cast hquot)
    have htoplim : Order.IsSuccLimit (P+Ordinal.omega0^a0*((X/v : Nat) : Ordinal)) :=
      Ordinal.isSuccLimit_add P (Ordinal.isSuccLimit_mul_left
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 ha0pos.ne') (by exact_mod_cast hquotpos))
    have hfixed : actualLimitPart (P+Ordinal.omega0^a0*((X/v : Nat) : Ordinal)) =
        P+Ordinal.omega0^a0*((X/v : Nat) : Ordinal) := by simpa using limitPart_tail _ htoplim 0
    rw [htop,hfixed]
    have hsmall : actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^(a0+1)) (X-1)) <
        P+Ordinal.omega0^a0*((X/v : Nat) : Ordinal) :=
      (Ordinal.mul_div_le _ Ordinal.omega0).trans_lt ((add_lt_add_iff_left P).mpr hlt)
    exact Ne.symm (ne_of_lt hsmall)
  · have hlt := (limitLocalTail a ha hlim).2 (X-1) X (by omega) (by omega)
    have hsmall : Ordinal.omega0 < Ordinal.omega0^a := by
      have h1 : (1 : Ordinal) < a := lt_of_lt_of_le (by norm_num) h2
      simpa using (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono h1
    have hnormomega : actualOrdinalNorm Ordinal.omega0=2 := by simpa using actualFiniteHeadNorm 1 0
    have hb : ∀ b : Nat, 2 ≤ b → Ordinal.omega0 ≤ actualMaximumPredecessor (Ordinal.omega0^a) b := by
      intro b hb
      exact (actualMaximumPredecessor_correct _ (Ordinal.opow_pos a Ordinal.omega0_pos) hpow b).2
        ⟨hsmall,by rwa [hnormomega]⟩
    have hxBelow := (actualMaximumPredecessor_correct _ (Ordinal.opow_pos a Ordinal.omega0_pos) hpow X).1.1.trans hpow
    have hyBelow := (actualMaximumPredecessor_correct _ (Ordinal.opow_pos a Ordinal.omega0_pos) hpow (X-1)).1.1.trans hpow
    rw [phase_limit_add P _ hxBelow (hb X (by omega)),phase_limit_add P _ hyBelow (hb (X-1) (by omega))]
    intro heq
    have heq' := congrArg (Ordinal.log Ordinal.omega0) (add_left_cancel heq)
    rw [← phase_limit_log _ hxBelow (hb X (by omega)),← phase_limit_log _ hyBelow (hb (X-1) (by omega))] at heq'
    exact (ne_of_lt hlt) heq'.symm

end LogicLineages.PermittedControl
