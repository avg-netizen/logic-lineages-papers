module
public import LogicLineages.ModelsAlgebra.PGroups.RawBoundedClassificationTargets
public import LogicLineages.ModelsAlgebra.PGroups.BoundedInfiniteRank
public import LogicLineages.ModelsAlgebra.PGroups.SourceTwoInfinite
public import LogicLineages.ModelsAlgebra.PGroups.SourceSigmaThree
public import LogicLineages.ModelsAlgebra.PGroups.RawSourceOneInfinite
public import LogicLineages.ModelsAlgebra.PGroups.RawBoundedLower
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem raw_bounded_classification : Targets.groupRawBoundedClassification := by
  classical
  intro p _ G _ _ _ N hN
  by_cases htwo : ∃ a b : Fin N, a < b ∧
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup G)) = Cardinal.aleph0 ∧
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup G)) = Cardinal.aleph0
  · obtain ⟨a,b,hab,ha,hb⟩ := htwo
    obtain ⟨hu,hl⟩ := raw_source_two_infinite_scott_bounds p G N a b hab hN ha hb
    exact Or.inl ⟨a,b,hab,ha,hb,hu,raw_source_two_infinite_no_sigma_three p G N a b hab hN ha hb,hl⟩
  · obtain ⟨a,ha⟩ := bounded_infinite_rank_exists p G N hN
    have huniq (j : Fin N) (hj : Module.rank (ZMod p)
        (UlmLayer p (finiteFiltration p j.val : AddSubgroup G)) = Cardinal.aleph0) : j = a := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hja | haj
      · exact htwo ⟨j,a,hja,hj,ha⟩
      · exact htwo ⟨a,j,haj,ha,hj⟩
    let k := a.val+1
    have hk : 0 < k := Nat.succ_pos _
    have hkN : k ≤ N := Nat.succ_le_of_lt a.isLt
    have hidx : k-1 = a.val := Nat.add_sub_cancel a.val 1
    have hi : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0 :=
      (congrArg (fun j : ℕ => Module.rank (ZMod p)
        (UlmLayer p (finiteFiltration p j : AddSubgroup G))) hidx).trans ha
    have hf (j : ℕ) (hjN : j < N) (hjk : j ≠ k-1) : Module.rank (ZMod p)
        (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0 := by
      apply lt_of_le_of_ne (countable_ulm_rank_bound p G j)
      intro hj
      have he := congrArg Fin.val (huniq ⟨j,hjN⟩ hj)
      exact hjk (he.trans hidx.symm)
    by_cases hp : ∃ j : ℕ, j < k-1 ∧ Module.rank (ZMod p)
        (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≠ 0
    · obtain ⟨hu,hSigma,hPi⟩ := raw_source_positive_lower_scott_bounds p G k N hk hkN hN hi hf hp
      exact Or.inr (Or.inl ⟨k,hk,hkN,hi,hf,hp,hu,hSigma,hPi⟩)
    · have hz (j : ℕ) (hj : j < k-1) : Module.rank (ZMod p)
          (UlmLayer p (finiteFiltration p j : AddSubgroup G)) = 0 := by
        by_contra hne
        exact hp ⟨j,hj,hne⟩
      obtain ⟨hu,hPi,hd⟩ := raw_source_zero_lower_scott_bounds p G k N hk hkN hN hi hf hz
      exact Or.inr (Or.inr ⟨k,hk,hkN,hi,hf,hz,hu,raw_bounded_no_sigma_two_scott p G N hN,hPi,hd⟩)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
