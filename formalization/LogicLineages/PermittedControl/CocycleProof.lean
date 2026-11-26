module
public import LogicLineages.PermittedControl.CocycleTargets
public import LogicLineages.PermittedControl.PureCertificateClockProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem limit_interval_separation (mu kappa : Ordinal.{0})
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hk : Order.IsSuccLimit kappa) (hmk : mu<kappa) :
    mu+Ordinal.omega0 ≤ kappa := by
  by_contra h
  have he := (interval_iff_limitPart kappa mu hmud).mp ⟨hmk.le,lt_of_not_ge h⟩
  have he' : actualLimitPart kappa=kappa := by simpa only [Nat.cast_zero,add_zero] using limitPart_tail kappa hk 0
  rw [he'] at he
  exact hmk.ne he.symm

 theorem actualAffordableCocycle : Targets.ActualAffordableCocycle := by
  intro f B hf mu kappa lambda t hmu hk hl hmud hkl hll hmk hklam ht
  have had := selected_threshold_admissible f B hf
  have hA := count_initial_facts lambda t hl hll (by omega)
  obtain ⟨i,hi,hiN⟩ := entry_exists_state f had.2 kappa (Or.inr hkl) (countInitial lambda t) hA.1
    (hklam.le.trans le_self_add) (by rw [hA.2.1]; omega)
  let h := entryNormAt f (countInitial lambda t) i
  have hnorm : h=f^[i] t := by simpa only [h,hA.2.1] using hiN
  have hgrow : t ≤ h := by rw [hnorm]; exact iterate_self_le (control_self_le f had.2) i t
  have hreset := actual_entry_reset f (countInitial lambda t) kappa i h hk hi rfl
  have hK := count_initial_facts kappa h hk hkl (by omega)
  obtain ⟨j,hj,hjN⟩ := entry_exists_state f had.2 mu hmud (countInitial kappa h) hK.1
    (hmk.le.trans le_self_add) (by rw [hK.2.1]; omega)
  have hfirst : FirstEntry f (countInitial lambda t) mu (i+j) :=
    firstEntry_compose f (countInitial lambda t) kappa mu i j hA.1
      (limit_interval_separation mu kappa hmud hkl hmk) hi (by rwa [hreset])
  have hcontinuation : entryNormAt f (countInitial lambda t) (i+j)=entryNormAt f (countInitial kappa h) j := by
    unfold entryNormAt
    rw [actual_entry_reset_continuation f (countInitial lambda t) kappa i h j hk hi rfl]
  refine ⟨i,j,i+j,hi,hj,hfirst,hreset,rfl,hcontinuation,hnorm,?_,?_⟩
  · simpa only [hK.2.1] using hjN
  · rw [hcontinuation,hjN,hK.2.1,hnorm,Nat.add_comm i j,Function.iterate_add_apply]

end LogicLineages.PermittedControl
