module
public import LogicLineages.PermittedControl.LinearReturnTargets
public import LogicLineages.PermittedControl.SensitiveSetupProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem linear_return_one (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu P A : Ordinal.{0}) (k t : Nat) (hmu : mu < epsilonZero) (hP : P < epsilonZero)
    (hA : A < epsilonZero) (hPl : Order.IsSuccLimit P)
    (hpart : actualLimitPart A=mu+(P+Ordinal.omega0*(k : Ordinal))) (hnorm : actualOrdinalNorm A=t) :
    FirstEntry f A (mu+P) k ∧ actualOrdinalNorm ((descentWith f)^[k] A)=f^[k] t ∧
    actualLimitPart ((descentWith f)^[k] A-mu)=P := by
  have htarget := epsilonZero_add_principal hmu hP
  have htargetl := Ordinal.isSuccLimit_add mu hPl
  have hheadl : Order.IsSuccLimit (mu+(P+Ordinal.omega0*(k : Ordinal))) := by
    by_cases hk : k=0
    · simpa [hk] using htargetl
    · have hkpos : 0 < (k : Ordinal.{0}) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
      exact Ordinal.isSuccLimit_add mu (Ordinal.isSuccLimit_add P
        (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hkpos))
  have hinterval := (interval_iff_limitPart A _ (Or.inr hheadl)).mpr hpart
  obtain ⟨n,hn⟩ := interval_tail A _ hinterval.1 hinterval.2
  have hentry : FirstEntry f A (mu+P) k := by
    rw [hn]
    simpa only [add_assoc] using linear_entry f (selected_threshold_admissible f B hf).2
      (mu+P) (Or.inr htargetl) htarget k n
  have hnon : Ordinal.omega0 ≤ (descentWith f)^[k] A :=
    (Ordinal.omega0_le_of_isSuccLimit htargetl).trans hentry.1
  have horbit := trajectory_norm_nonfinite f A hA k hnon
  rw [hnorm] at horbit
  obtain ⟨m,hm⟩ := interval_tail _ (mu+P) hentry.1 hentry.2.1
  refine ⟨hentry,horbit,?_⟩
  rw [hm,add_assoc,Ordinal.add_sub_cancel]
  exact limitPart_tail P hPl m

 theorem actualLinearReturn : Targets.ActualLinearReturn := by
  intro f B hf mu nu P A A' k t hmu hnu hP hA hA' hPl hpart hpart' hn hn' ht
  have h := linear_return_one f B hf mu P A k t hmu hP hA hPl hpart hn
  have h' := linear_return_one f B hf nu P A' k t hnu hP hA' hPl hpart' hn'
  exact ⟨h.1,h'.1,h.2.1,h'.2.1,h.2.2,h'.2.2⟩

end LogicLineages.PermittedControl
