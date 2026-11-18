module
public import LogicLineages.PermittedControl.InitialNoSensitiveProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- An exceptional actual quadratic top is followed through its generated
linear tail, with a genuine common return time. -/
 theorem quadratic_exception_return (f : Nat → Nat) (B : Nat)
    (mu nu P A A' : Ordinal.{0}) (R t : Nat)
    (hs : Targets.SensitiveUnitSetup f B mu nu P 2 0 A A' R t)
    (hex : relativeProfile nu (Ordinal.log Ordinal.omega0 P)=relativeProfile mu (Ordinal.log Ordinal.omega0 P)+1 ∧
      (relativeProfile mu (Ordinal.log Ordinal.omega0 P)+actualOrdinalNorm P)%2=1) :
    ∃ j : Nat, FirstEntry f A (mu+P) j ∧ FirstEntry f A' (nu+P) j ∧
      actualOrdinalNorm ((descentWith f)^[j] A)=f^[j] t ∧
      actualOrdinalNorm ((descentWith f)^[j] A')=f^[j] t := by
  have hs0 := hs
  rcases hs with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hd,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hn,hn',hcd⟩
  have hPl := retained_prefix_limit P 2 hPpos (by norm_num) hd
  have heq := (quadraticUnitTop f B mu nu P A A' R t hs0).mpr hex
  have hstep := sensitive_top_step f B mu nu P 2 A A' R t hs0
  let X := f t-relativeProfile mu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P
  have hcR := (relativePrefixNorm mu (Ordinal.log Ordinal.omega0 P) hmu).2.2.trans hmuR
  have htlarge := sensitive_tail_large R B t ht
  have hu := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hform : actualLimitPart (descentWith f A-mu)=P+Ordinal.omega0*((X/2 : Nat) : Ordinal) := by
    rw [hstep.1,actualOmegaSquaredMaximum X hX,← add_assoc]
    have hq : 0 < ((X/2 : Nat) : Ordinal) := by exact_mod_cast (show 0 < X/2 by omega)
    exact limitPart_tail _ (Ordinal.isSuccLimit_add P
      (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hq)) _
  have hform' := heq.symm.trans hform
  have hnext : descentWith f A < epsilonZero := (descent_le f A hA).trans_lt hA
  have hnext' : descentWith f A' < epsilonZero := (descent_le f A' hA').trans_lt hA'
  have hnon : Ordinal.omega0 ≤ P+Ordinal.omega0*((X/2 : Nat) : Ordinal) :=
    (Ordinal.omega0_le_of_isSuccLimit hPl).trans le_self_add
  have hpartnext := absolute_limit_of_relative mu (descentWith f A) hnext ((by rwa [hform] : Ordinal.omega0 ≤ actualLimitPart (descentWith f A-mu)).trans (Ordinal.mul_div_le _ _))
  have hpartnext' := absolute_limit_of_relative nu (descentWith f A') hnext' ((by rwa [hform'] : Ordinal.omega0 ≤ actualLimitPart (descentWith f A'-nu)).trans (Ordinal.mul_div_le _ _))
  rw [hform] at hpartnext
  rw [hform'] at hpartnext'
  have hgenl : Order.IsSuccLimit (P+Ordinal.omega0*((X/2 : Nat) : Ordinal)) :=
    Ordinal.isSuccLimit_add P (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
      (by exact_mod_cast (show 0 < X/2 by omega)))
  have hhead := actual_limit_norm_le _ _ hnext (Ordinal.isSuccLimit_add mu hgenl) hpartnext
  have hhead' := actual_limit_norm_le _ _ hnext' (Ordinal.isSuccLimit_add nu hgenl) hpartnext'
  rw [hstep.2.2.1] at hhead
  rw [hstep.2.2.2.1] at hhead'
  have htm := relativeNorm mu P hmu hP
  have htn := relativeNorm nu P hnu hP
  have hguard : max 2 (max (actualOrdinalNorm (mu+(P+Ordinal.omega0*((X/2 : Nat) : Ordinal))))
      (max (actualOrdinalNorm (nu+(P+Ordinal.omega0*((X/2 : Nat) : Ordinal))))
        (max (actualOrdinalNorm (mu+P)+3) (actualOrdinalNorm (nu+P)+3)))) ≤ f t := by omega
  have hret := actualLinearReturn f B hf mu nu P (descentWith f A) (descentWith f A') (X/2) (f t)
    hmu hnu hP hnext hnext' hPl hpartnext hpartnext' hstep.2.2.1 hstep.2.2.2.1 hguard
  have hw : Ordinal.omega0 ≤ Ordinal.omega0^(2 : Ordinal) := Ordinal.left_le_opow _ (by norm_num)
  have hskip : (mu+P)+Ordinal.omega0 ≤ A := by
    have h := (Ordinal.mul_div_le A Ordinal.omega0)
    change actualLimitPart A ≤ A at h
    rw [hpart,add_zero] at h
    exact (by simpa only [add_assoc] using (add_le_add_iff_left (mu+P)).mpr hw).trans h
  have hskip' : (nu+P)+Ordinal.omega0 ≤ A' := by
    have h := (Ordinal.mul_div_le A' Ordinal.omega0)
    change actualLimitPart A' ≤ A' at h
    rw [hpart',add_zero] at h
    exact (by simpa only [add_assoc] using (add_le_add_iff_left (nu+P)).mpr hw).trans h
  refine ⟨1+X/2,firstEntry_prepend f A (mu+P) _ hskip hret.1,
    firstEntry_prepend f A' (nu+P) _ hskip' hret.2.1,?_,?_⟩
  · simpa only [Nat.add_comm 1,Function.iterate_succ_apply] using hret.2.2.1
  · simpa only [Nat.add_comm 1,Function.iterate_succ_apply] using hret.2.2.2.1

end LogicLineages.PermittedControl
