module
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorParityTargets
public import Mathlib.Tactic.NormNum
public import Mathlib.SetTheory.Ordinal.Principal
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
theorem countable_successor_parity : Targets.countableSuccessorParity := by
  intro β hc
  let lam : Ordinal := Ordinal.omega0*(β/Ordinal.omega0)
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt β Ordinal.omega0_ne_zero)
  have he : β=lam+m := by rw [←hm]; exact (Ordinal.div_add_mod β Ordinal.omega0).symm
  let k := m/2
  let γ : Ordinal := lam+k
  have hle : γ≤β+1 := by
    apply le_trans _ (le_self_add : β≤β+1)
    rw [he]
    exact (add_le_add_iff_left lam).mpr (by exact_mod_cast Nat.div_le_self m 2)
  have hcount : Countable γ.ToType := by
    letI := hc
    apply Cardinal.mk_le_aleph0_iff.mp
    rw [Cardinal.mk_toType]
    exact (Ordinal.card_le_card hle).trans (by simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α:=(β+1).ToType)))
  have htwo : (2:Ordinal.{0})*Ordinal.omega0=Ordinal.omega0 := by
    exact_mod_cast Ordinal.natCast_mul_omega0 (by decide:0<(2:ℕ))
  have hγ : 2*γ=lam+(2*k:ℕ) := by
    change 2*(lam+(k:Ordinal))=lam+((2*k:ℕ):Ordinal)
    rw [mul_add]
    have hlam : 2*lam=lam := by change 2*(Ordinal.omega0*(β/Ordinal.omega0))=_; rw [←mul_assoc,htwo]
    rw [hlam,Ordinal.natCast_mul,Nat.cast_ofNat]
  have hmod := Nat.mod_lt m (by decide:0<2)
  have hdecomp := Nat.mod_add_div m 2
  refine ⟨γ,hcount,?_⟩
  by_cases hz:m%2=0
  · left
    have hm' : m=2*k := by dsimp only [k]; omega
    rw [he,hm',hγ]
  · right
    have hm' : m=2*k+1 := by dsimp only [k]; omega
    rw [he,hm',hγ,Nat.cast_add,Nat.cast_one]
    simp only [add_assoc,one_add_one_eq_two]
end LogicLineages.ModelsAlgebra.PGroups
