module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirRankTargets
public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclicDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupTwoReservoirExtraction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ)
    (a b : Fin N), a < b → (∀ x : G, p ^ N • x = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup G)) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup G)) = Cardinal.aleph0 →
    ∃ (A : Type) (inst : AddCommGroup A), letI := inst;
      Countable A ∧
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup A)) = 0 ∧
      Nonempty (G ≃+ ReservoirGroup A (ZMod (p^(a.val+1))) (ZMod (p^(b.val+1))))

end LogicLineages.ModelsAlgebra.PGroups.Targets
