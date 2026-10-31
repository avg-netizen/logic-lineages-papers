module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerSubtreeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Every ancestor-preserving finite tree inclusion induces a faithful map of
actual presented groups. No group map or injectivity oracle is supplied. -/
def walkerFiniteSubtreeEmbedding : Prop :=
  ∀ p : ℕ, 0 < p → ∀ A B : WalkerParentSequence, ∀ n m : ℕ,
    ∀ e : Fin n ↪ Fin m,
      (∀ i, walkerParentNode B m (e i) = (walkerParentNode A n i).map e) →
      ∃ f : (walkerFinitePresentation p A n).Carrier →+
          (walkerFinitePresentation p B m).Carrier,
        Function.Injective f ∧
        ∀ i, f ((walkerFinitePresentation p A n).generator i) =
          (walkerFinitePresentation p B m).generator (e i)

end LogicLineages.ModelsAlgebra.PGroups.Targets
