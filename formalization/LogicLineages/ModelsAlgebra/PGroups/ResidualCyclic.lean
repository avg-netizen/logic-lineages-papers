module
public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclicTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssembly
public import LogicLineages.ModelsAlgebra.PGroups.CyclicUlm
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem residual_cyclic_exponent : Targets.groupResidualCyclicExponent := by
  intro p N I a b x
  funext l
  ext n
  exact power_cyclic_annihilation p (l.val.val+1) N (Nat.succ_le_of_lt l.val.isLt) (x l n)

theorem residual_cyclic_rank : Targets.groupResidualCyclicRank := by
  classical
  intro p _ N I a b j
  let L := {l : Fin N // l ≠ a ∧ l ≠ b}
  rw [pi_ulm_rank]
  have hr (l : L) : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val :
      AddSubgroup (I l.val →₀ ZMod (p^(l.val.val+1))))) =
      if l.val = j then Cardinal.mk (I j) else 0 := by
    rw [finsupp_ulm_rank, cyclic_ulm_rank]
    by_cases h : l.val = j
    · subst j
      simp
    · have hv : j.val+1 ≠ l.val.val+1 := by
        intro he
        exact h (Fin.ext (Nat.succ.inj he).symm)
      have hv0 : j.val ≠ l.val.val := fun he => h (Fin.ext he.symm)
      simp [h,hv,hv0]
  simp_rw [hr]
  have hc (l : L) : (if l.val = j then Cardinal.mk (I j) else 0) =
      Cardinal.mk {x : I j // l.val = j} := by
    by_cases h : l.val = j
    · rw [if_pos h]
      exact (Cardinal.mk_congr (Equiv.subtypeUnivEquiv (fun _ => h))).symm
    · rw [if_neg h]
      haveI : IsEmpty {x : I j // l.val = j} := ⟨fun x => h x.property⟩
      simp
  simp_rw [hc]
  rw [← Cardinal.mk_sigma]
  by_cases hj : j = a ∨ j = b
  · rw [if_pos hj]
    haveI : IsEmpty (Σ l : L, {x : I j // l.val = j}) := ⟨by
      rintro ⟨l,x⟩
      rcases hj with ha | hb
      · exact l.property.1 (x.property.trans ha)
      · exact l.property.2 (x.property.trans hb)⟩
    simp
  · rw [if_neg hj]
    let lj : L := ⟨j, not_or.mp hj⟩
    let e : (Σ l : L, {x : I j // l.val = j}) ≃ I j :=
      { toFun := fun x => x.2.val
        invFun := fun x => ⟨lj,⟨x,rfl⟩⟩
        left_inv := by
          rintro ⟨l,x⟩
          have hl : l = lj := Subtype.ext x.property
          subst l
          rfl
        right_inv := fun _ => rfl }
    exact Cardinal.mk_congr e

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
