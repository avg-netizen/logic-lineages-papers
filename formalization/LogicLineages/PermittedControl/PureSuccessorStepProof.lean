module
public import LogicLineages.PermittedControl.PureMaximumBandProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualPureSuccessorStep : Targets.ActualPureSuccessorStep := by
  intro f B hf mu beta A R t hmu hb hA hmud hb2 hR hmuR hbR ht hp hn
  let X := f t-relativeProfile mu beta
  let v := 1+actualOrdinalNorm beta
  let q := X/v
  let r := actualMaximumPredecessor (Ordinal.omega0^beta) (X%v)
  have hbetapos : 0 < beta := (by norm_num : (0 : Ordinal) < 2).trans_le hb2
  have hP := phase_power_below beta hb
  have hbs : beta+1 < epsilonZero := by simpa using (actualFiniteTailClosureNorm beta hb 1).1
  have hY := phase_power_below (beta+1) hbs
  have hYP : 0 < beta+1 := hbetapos.trans_le le_self_add
  have hYl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hYP.ne'
  have hheadl := Ordinal.isSuccLimit_add mu hYl
  have hnon : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit hheadl).trans
    (by rw [← hp]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have hu := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  have hlarge := sensitive_tail_double R B t ht
  have hcR := (relativePrefixNorm mu beta hmu).2.2.trans hmuR
  have hPN : actualOrdinalNorm (Ordinal.omega0^beta)=1+actualOrdinalNorm beta := by
    simpa only [Nat.cast_one,mul_one,one_mul] using thick_monomial_norm beta hb 1
  have hnorm := relativeNorm mu (Ordinal.omega0^beta) hmu hP
  have hPb : actualOrdinalNorm (mu+Ordinal.omega0^beta) ≤ f t := by omega
  have hmub : actualOrdinalNorm mu ≤ f t := by omega
  have hlocal := pure_successor_maximum mu beta (f t) hmu hb hmub hPb
  have hnext : descentWith f A-mu=actualMaximumPredecessor (Ordinal.omega0^(beta+1)) X := by
    unfold descentWith
    rw [hp,hn]
    exact hlocal
  have hX : v ≤ X := by dsimp only [X,v]; omega
  have hq := pure_quotient_large R B t (f t) (relativeProfile mu beta) v ht hu hcR (by dsimp only [v]; omega) (by dsimp only [v]; omega)
  change R+2 < q at hq
  have hqpos : 0 < q := by omega
  have hform : descentWith f A-mu=Ordinal.omega0^beta*(q : Ordinal)+r := by
    rw [hnext,successorLocalTail beta X hb hX]
  have hr : r < Ordinal.omega0^beta :=
    (actualMaximumPredecessor_correct _ (Ordinal.opow_pos _ Ordinal.omega0_pos) hP (X%v)).1.1
  have hrb := hr.trans hP
  have hqn : (q : Ordinal) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hqp : 0 < (q : Ordinal) := by exact_mod_cast hqpos
  have hblockl : Order.IsSuccLimit (Ordinal.omega0^beta*(q : Ordinal)) :=
    Ordinal.isSuccLimit_mul_left (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hbetapos.ne') hqp
  refine ⟨hform,?_,hq,hr,?_,?_⟩
  · rw [descent_norm f A hnon hA,hn]
  · rw [hform,Ordinal.log_opow_mul_add Ordinal.one_lt_omega0 hqn hr,
      Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 q),add_zero]
  · rw [hform,limitPart_add_limit_left _ r hblockl hrb]

end LogicLineages.PermittedControl
