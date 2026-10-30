module
public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclicDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def groupSingleReservoirExtraction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [AddCommGroup K] [Countable K] (N : ℕ) (a : Fin N),
    (∀ x : K, p^N • x = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup K)) = Cardinal.aleph0 →
    ∃ (A : Type) (inst : AddCommGroup A), letI := inst;
      Countable A ∧ Nonempty (K ≃+ A × (ℕ →₀ ZMod (p^(a.val+1))))

end LogicLineages.ModelsAlgebra.PGroups.Targets
