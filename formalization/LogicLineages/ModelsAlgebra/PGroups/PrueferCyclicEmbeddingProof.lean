module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferCyclicEmbeddingTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferModelProof
public import LogicLineages.ModelsAlgebra.PGroups.CyclicRoot
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
theorem pruefer_cyclic_embedding : Targets.prueferCyclicEmbedding := by
  intro p _ j
  obtain ⟨t,ht,hpt⟩ := (genuine_pruefer_model p).2.2
  obtain ⟨y,hy⟩ := (genuine_pruefer_model p).2.1 (p^j)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) t
  have hy0 : p^(j+1) • y = 0 := by
    rw [pow_succ,mul_nsmul,hy,hpt]
  refine ⟨cyclicRootHom (p^(j+1)) (PrueferModel p) y hy0,?_⟩
  apply cyclic_root_injective p (PrueferModel p) j y hy0
  rw [hy]
  exact ht
end LogicLineages.ModelsAlgebra.PGroups
