module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedReservoirEmbeddingTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicClassification
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteUlm
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesDefinitions
public import Mathlib.Data.Finsupp.ToDFinsupp
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem bounded_reservoir_embedding : Targets.groupBoundedReservoirEmbedding := by
  classical
  intro p _ T _ _ k hk
  obtain ⟨I,⟨e⟩,hI⟩ := bounded_cyclic_calibrated_decomposition p T k hk
  letI (l : Fin k) : Countable (I l) := Cardinal.mk_le_aleph0_iff.mp
    ((hI l).le.trans (countable_ulm_rank_bound p T l.val))
  let J := Σ l : Fin k, I l
  let C := ZMod (p^k)
  let d : CyclicRootSum p k I →+ (Π₀ _ : J, C) := DFinsupp.mapRange.addMonoidHom
    (fun a : J => powerCyclicInclusion p (a.1.val+1) k (Nat.succ_le_of_lt a.1.isLt))
  have hd : Function.Injective d := by
    intro x y h
    ext a
    have he := congrArg (fun z : Π₀ _ : J, C => z a) h
    exact power_cyclic_inclusion_injective p (a.1.val+1) k (Nat.succ_le_of_lt a.1.isLt) he
  let c : (Π₀ _ : J, C) ≃+ (J →₀ C) := finsuppAddEquivDFinsupp.symm
  let r : (J →₀ C) →+ (ℕ →₀ C) := Finsupp.mapDomain.addMonoidHom (branchEncoding J)
  have hr : Function.Injective r := Finsupp.mapDomain_injective (branchEncoding J).injective
  exact ⟨r.comp (c.toAddMonoidHom.comp (d.comp e.toAddMonoidHom)),
    hr.comp (c.injective.comp (hd.comp e.injective))⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
