module
public import LogicLineages.PermittedControl.PureCertificateCodeProof
public import LogicLineages.PermittedControl.DivergenceEntryProof
public import LogicLineages.PermittedControl.PureSuccessorSeparationProof
public import LogicLineages.PermittedControl.PureLimitProof
public import LogicLineages.PermittedControl.HighestPhaseGeometryProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem entry_order_from_oriented (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P A A' : Ordinal.{0}) (t tau sigma : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hP : Ordinal.omega0 ≤ P) (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hmuN : actualOrdinalNorm mu ≤ t) (hnuN : actualOrdinalNorm nu ≤ t)
    (hHit : FirstEntry f A mu tau) (hHit' : FirstEntry f A' nu sigma)
    (hdiv : Targets.OrientedUnitDivergence f mu nu P A A') :
    entryNormAt f A' sigma < entryNormAt f A tau := by
  obtain ⟨i,hcmp,hkeep',hkeep⟩ := hdiv
  have hnon : Ordinal.omega0 ≤ (descentWith f)^[i] A :=
    (hP.trans hkeep).trans ((Ordinal.mul_div_le _ _).trans (Ordinal.sub_le_self _ _))
  have hnon' : Ordinal.omega0 ≤ (descentWith f)^[i] A' :=
    (hP.trans hkeep').trans ((Ordinal.mul_div_le _ _).trans (Ordinal.sub_le_self _ _))
  have hNi : actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t := by
    rw [trajectory_norm_nonfinite f A hA i hnon,hn]
  have hNi' : actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t := by
    rw [trajectory_norm_nonfinite f A' hA' i hnon',hn']
  have hgrow := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
  obtain ⟨s,r,his,hsr,hs,hr,_,_,horder⟩ := actualDivergenceEntryOrder f B hf nu mu A' A i (f^[i] t)
    hnu hmu hA' hA hnud hmud hNi' hNi (hnuN.trans hgrow) (hmuN.trans hgrow)
    (Ordinal.omega0_pos.trans_le (hP.trans hkeep')) hcmp
  have he := firstEntry_unique f A mu r tau hr hHit
  have he' := firstEntry_unique f A' nu s sigma hs hHit'
  simpa only [he,he'] using horder

 theorem first_entry_norm_of_hit (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu A : Ordinal.{0}) (t i : Nat) (hA : A < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hmuA : mu ≤ A)
    (hn : actualOrdinalNorm A=t) (hbudget : actualOrdinalNorm mu ≤ t)
    (hHit : FirstEntry f A mu i) : entryNormAt f A i=f^[i] t := by
  obtain ⟨j,hj,hNj⟩ := entry_exists_state f (selected_threshold_admissible f B hf).2 mu hmud A hA hmuA (by omega)
  have he := firstEntry_unique f A mu j i hj hHit
  simpa only [he,hn] using hNj

 theorem compose_pure_entry (f : Nat → Nat) (mu E A : Ordinal.{0}) (i j : Nat)
    (hA : A < epsilonZero) (hE : 1 ≤ E)
    (hfirst : FirstEntry f A (mu+Ordinal.omega0^E) i)
    (hnext : FirstEntry f ((descentWith f)^[i] A) mu j) : FirstEntry f A mu (i+j) := by
  apply firstEntry_compose f A (mu+Ordinal.omega0^E) mu i j hA _ hfirst hnext
  apply add_le_add_right
  simpa only [Ordinal.opow_one] using (Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone hE

end LogicLineages.PermittedControl
