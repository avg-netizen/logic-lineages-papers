module
public import LogicLineages.ModelsAlgebra.PGroups.NextBlockUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.InternalProduct
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.TerminalLayer
public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssembly
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe v

theorem quotient_next_block_ulm_inequality : Targets.groupQuotientNextBlockUlmInequality.{v} := by
  intro G _ p _ δ K T hH hKT j
  let H := (transfiniteFiltration p δ : AddSubgroup G)
  let QH := (transfiniteFiltration p δ : AddSubgroup (G ⧸ T))
  rw [← transfinite_tail_ulm_rank (G ⧸ T) p δ (j : Ordinal.{v}),
    ← transfinite_tail_ulm_rank G p δ (j : Ordinal.{v}),
    finite_ordinal_filtration, finite_ordinal_filtration]
  obtain ⟨e⟩ := terminal_layer_quotient G p δ K T hH hKT
  obtain ⟨f,_⟩ := internal_product_isomorphism G K T H hH hKT
  calc
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup QH)) =
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup K)) :=
      GroupInfinitary.isomorphism_ulm_rank QH K e p j
    _ ≤ Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup K)) +
        Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup T)) := le_self_add
    _ = Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (K × T))) :=
      (GroupInfinitary.product_ulm_rank p K T j).symm
    _ = Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup H)) :=
      GroupInfinitary.isomorphism_ulm_rank (K × T) H f p j

end LogicLineages.ModelsAlgebra.PGroups
