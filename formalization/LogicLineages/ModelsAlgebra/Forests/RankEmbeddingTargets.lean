module

public import LogicLineages.ModelsAlgebra.Forests.ThickeningDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ClusterCompletenessDefinitions

/-! Calibrated actual cluster maps lift to actual order embeddings into a
proved finite thickening. All map calibrations are explicit intermediate
hypotheses, subsequently to be paid by concrete comb-template constructions. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

def ClusterRankEmbedding : Prop :=
  ∀ (F T H : FiniteOrderForest) (n : Nat)
    (points : (T.Carrier × Fin n) ≃ H.Carrier) (q : F.Carrier → T.Carrier),
    (∀ x y, points x ≤ points y ↔ thickLE T n x y) →
    (∀ x y, q x ≤ q y ↔ finiteLeafCluster F y ⊆ finiteLeafCluster F x) →
    (∀ x y, q x = q y ↔ finiteLeafCluster F x = finiteLeafCluster F y) →
    Fintype.card F.Carrier ≤ n → Nonempty (F.Carrier ↪o H.Carrier)

end LogicLineages.ModelsAlgebra.Forests.Targets
