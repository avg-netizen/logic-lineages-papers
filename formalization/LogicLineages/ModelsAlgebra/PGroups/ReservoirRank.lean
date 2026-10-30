module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirRankTargets
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirStage
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRankAssembly
public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem reservoir_whole_rank : Targets.groupReservoirWholeRank := by
  intro p _ A _ ell m hell hm hA
  change Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell-1) :
    AddSubgroup (A × ((ℕ →₀ ZMod (p^ell)) × (ℕ →₀ ZMod (p^m)))))) = _
  rw [product_ulm_rank, product_ulm_rank, hA, infinite_cyclic_ulm_rank, infinite_cyclic_ulm_rank]
  have h1 : ell-1+1=ell := by omega
  have h2 : ell-1+1≠m := by omega
  simp [h1,h2,ne_of_lt hm]

theorem reservoir_stage_rank : Targets.groupReservoirStageRank := by
  intro p _ A _ ell m hell hm hA i
  obtain ⟨e⟩ := reservoir_stage_isomorphism A (ZMod (p^ell)) (ZMod (p^m)) i
  rw [isomorphism_ulm_rank _ _ e p (ell-1), product_ulm_rank, product_ulm_rank, hA,
    finite_cyclic_ulm_rank, infinite_cyclic_ulm_rank]
  have h1 : ell-1+1=ell := by omega
  have h2 : ell-1+1≠m := by omega
  simp [h1,h2,ne_of_lt hm]

theorem reservoir_stage_nonisomorphism : Targets.groupReservoirStageNonisomorphism := by
  intro p _ A _ ell m hell hm hA i he
  obtain ⟨e⟩ := he
  have h := isomorphism_ulm_rank _ _ e p (ell-1)
  rw [reservoir_whole_rank p A ell m hell hm hA,
    reservoir_stage_rank p A ell m hell hm hA i] at h
  exact (Cardinal.nat_lt_aleph0 i).ne h.symm

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
