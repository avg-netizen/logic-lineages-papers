module
public import LogicLineages.PermittedControl.EntryLongProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

theorem entryResidues : Targets.EntryResidues := by
  intro f B hf m lam nu t hm ha hl hnu hlt ht
  have had := selected_threshold_admissible f B hf
  have hnuEps := hlt.trans ha
  have htail : max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm nu)) ≤ t := by omega
  obtain ⟨i,hi,horbit⟩ := entryExistenceOrbit f B hf lam nu t ha hl hnu hlt htail
  refine ⟨i,hi,horbit,?_,?_⟩
  · intro k hk heq
    have h := linear_entry f had.2 nu hnu hnuEps k (t-actualOrdinalNorm lam)
    have hstart : countInitial lam t = nu+(Ordinal.omega0*(k : Ordinal)+((t-actualOrdinalNorm lam : Nat) : Ordinal)) := by
      unfold countInitial
      rw [heq,add_assoc]
    rw [← hstart] at h
    exact firstEntry_unique f _ nu i k hi h
  · intro hlong
    obtain ⟨P,j,hP,hdiv,hnuEq,hnuNorm⟩ := target_prefix_decomposition nu hnu hnuEps
    have hbar := long_interval_above lam nu P j hnuEq hdiv hl hlt hlong
    have hinit := actualFiniteTailClosureNorm lam ha (t-actualOrdinalNorm lam)
    have hnorm : actualOrdinalNorm (countInitial lam t) = t := by
      change actualOrdinalNorm (lam+((t-actualOrdinalNorm lam : Nat) : Ordinal)) = t
      rw [hinit.2,Nat.add_sub_of_le (by omega)]
    have hlp : actualLimitPart (countInitial lam t) = lam := limitPart_tail lam hl _
    obtain ⟨q,hqpos,hq,hres⟩ := long_entry_state f B hf m hm nu P j hnu hP hdiv hnuEq hnuNorm
      (countInitial lam t) hinit.1 (by rwa [hlp]) (by rw [hnorm]; omega)
    have hiq := firstEntry_unique f _ nu i q hi hq
    subst q
    rw [hnorm] at hres
    refine ⟨hres,?_⟩
    have hp := selected_orbit f B hf m t i hm (by omega)
    rw [← horbit] at hp
    have hc := hres.sub_left (potential t : Int)
    have hpc : Int.ModEq (m : Int) (potential (entryNormAt f (countInitial lam t) i) : Int)
        (((actualOrdinalNorm nu+1)/2 : Nat) : Int) := by
      convert hp.trans hc using 1 <;> omega
    have heven : 2 ∣ entryNormAt f (countInitial lam t) i := by
      rw [horbit]
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      rw [hk,Function.iterate_succ_apply']
      exact selected_even f B hf _
    have hcast : (entryNormAt f (countInitial lam t) i : Int) =
        2 * (potential (entryNormAt f (countInitial lam t) i) : Int) := by
      have hmod := Nat.mod_eq_zero_of_dvd heven
      unfold potential
      omega
    rw [hcast]
    exact hpc.mul_left' (c := 2)

end LogicLineages.PermittedControl
