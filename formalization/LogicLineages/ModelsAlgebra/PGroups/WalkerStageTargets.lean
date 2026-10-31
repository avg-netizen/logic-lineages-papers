module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerStageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def walkerStageCoherence : Prop :=
  ∀ p : ℕ, ∀ parent : WalkerParentSequence,
    (∀ n, walkerStageMap p parent n n le_rfl = AddMonoidHom.id _) ∧
    (∀ n m k (hnm : n ≤ m) (hmk : m ≤ k),
      (walkerStageMap p parent m k hmk).comp (walkerStageMap p parent n m hnm) =
        walkerStageMap p parent n k (hnm.trans hmk))

def walkerStageFaithful : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence, ∀ n m (h : n ≤ m),
    Function.Injective (walkerStageMap p parent n m h)

def walkerStageGenerators : Prop :=
  ∀ p : ℕ, ∀ parent : WalkerParentSequence, ∀ n m (h : n ≤ m), ∀ i : Fin n,
    walkerStageMap p parent n m h ((walkerFinitePresentation p parent n).generator i) =
      (walkerFinitePresentation p parent m).generator (Fin.castLE h i)

end LogicLineages.ModelsAlgebra.PGroups.Targets
