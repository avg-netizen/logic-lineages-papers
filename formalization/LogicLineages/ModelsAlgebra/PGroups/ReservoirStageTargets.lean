module
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChainDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupReservoirStageIsomorphism : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (i : ℕ),
    Nonempty (reservoirStage A B C i ≃+ A × ((Fin i → B) × (ℕ →₀ C)))

end LogicLineages.ModelsAlgebra.PGroups.Targets
