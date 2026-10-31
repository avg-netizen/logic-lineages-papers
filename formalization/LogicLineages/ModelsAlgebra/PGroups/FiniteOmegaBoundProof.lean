module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
public import Mathlib.Data.Fintype.Order
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem omega_block_filtration : Targets.omegaBlockFiltration.{u,v} := by
  intro G _ p δ
  apply le_antisymm
  · apply le_iInf
    intro n
    apply transfiniteFiltration_antitone p
    rw [← Ordinal.iSup_add_natCast]
    exact Ordinal.le_iSup (fun n : ℕ => δ+(n:Ordinal.{v})) n
  · intro x hx
    rw [transfiniteFiltration_limit p (Ordinal.isSuccLimit_add δ Ordinal.isSuccLimit_omega0)]
    apply AddSubgroup.mem_iInf.mpr
    intro β
    have hcof : ∀ γ : Ordinal.{v}, γ < δ+Ordinal.omega0 →
        ∃ n : ℕ, γ < δ+(n:Ordinal.{v}) := by
      intro γ hγ
      rw [← Ordinal.iSup_add_natCast,Ordinal.lt_iSup_iff] at hγ
      exact hγ
    obtain ⟨n,hn⟩ := hcof β β.property
    exact transfiniteFiltration_antitone p hn.le ((AddSubgroup.mem_iInf.mp hx) n)

theorem finite_omega_block_bound : Targets.finiteOmegaBlockBound.{u,v} := by
  intro G _ p D _ δ
  classical
  have hex : ∀ x : D, ∃ n : ℕ,
      (x:G) ∈ transfiniteFiltration p (δ+(n:Ordinal.{v})) →
      (x:G) ∈ transfiniteFiltration p (δ+Ordinal.omega0) := by
    intro x
    by_cases hx : (x:G) ∈ transfiniteFiltration p (δ+Ordinal.omega0)
    · exact ⟨0,fun _ => hx⟩
    · have hn : ∃ n : ℕ, (x:G) ∉ transfiniteFiltration p (δ+(n:Ordinal.{v})) := by
        by_contra! h
        apply hx
        rw [omega_block_filtration G p δ]
        exact AddSubgroup.mem_iInf.mpr h
      obtain ⟨n,hn⟩ := hn
      exact ⟨n,fun h => False.elim (hn h)⟩
  choose k hk using hex
  obtain ⟨N,hN⟩ := Finite.exists_le k
  refine ⟨N,?_⟩
  intro n hn
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    apply hk ⟨x,hx.1⟩
    apply transfiniteFiltration_antitone p (add_le_add (le_refl δ) ?_) hx.2
    exact_mod_cast (hN ⟨x,hx.1⟩).trans hn
  · intro x hx
    refine ⟨hx.1,?_⟩
    apply transfiniteFiltration_antitone p ?_ hx.2
    rw [← Ordinal.iSup_add_natCast]
    exact Ordinal.le_iSup (fun n : ℕ => δ+(n:Ordinal.{v})) n

end LogicLineages.ModelsAlgebra.PGroups
