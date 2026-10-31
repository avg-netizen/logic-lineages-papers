module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferCyclicEmbeddingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def prueferCyclicEmbedding : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j : ℕ),
    ∃ f : ZMod (p^(j+1)) →+ PrueferModel p, Function.Injective f
end LogicLineages.ModelsAlgebra.PGroups.Targets
